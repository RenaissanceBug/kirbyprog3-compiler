#lang racket

(require "support/helpers.rkt"
         "support/env.rkt"
         )

(provide pass6 enforce-letrec-rule)

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

#|

An introduction:

Scheme's specification of letrec imposes this essential restriction:

  It must be possible to evaluate each of the expressions e_1 ... e_n
  in (letrec ([x_1 e_1] ... [x_n e_n]) body ...) without evaluating a
  reference or assignment to any of the variables x_1 ... x_n.

(References/assignments to those variables may occur in e_1 ... e_n, but they
may not be evaluated until after control has entered the body of the letrec.)
We'll call this "the letrec rule."  It is intended to prevent fragile code
like these two expressions:
  (letrec ([x 1] [y (+ x 1)]) (list x y))
  (letrec ([y (+ x 1)] [x 1]) (list x y))
It *seems* they should evaluate to '(1 2), but given that the order of
evaluation for the two <Decl>s in the letrec isn't specified, it's possible
for x to be undefined when (+ x 1) is evaluated.  So this is a violation of the
letrec rule, and as language implementors we should detect it and warn the
programmer rather than try to guess the intended meaning.

The *next* pass we write is going to perform an optimization by moving code
around, such that we won't necessarily be able to tell if the letrec rule is
being violated, so in *this* pass we will insert checks that will let the
runtime system tell if the letrec rule is being violated.

We could insert an explicit check for the undefined/void value before each
reference and assignment in the RHS expressions of the letrec, but that would
produce many more checks than we need, and would also obfuscate the code such
that it would be impossible to perform the optimizations we'll be implementing.
Instead, we have a better solution based on two observations:
  1) We can use a boolean flag to indicate whether a letrec-variable may be
     touched.
  2) We need only one such flag for each letrec-expression in the program.
|#

;; So, our transformation of letrec looks roughly like this:
#;#;#;
(letrec ([x_1 e_1] ... [x_n e_n]) body)
==> 
(let ([valid? #f])   ;; where valid? is a fresh identifier
  (letrec ([x_1 (recur-on e_1)]
           ...
           [x_n (recur-on e_n)])
    (begin (set! valid? #t)
           (recur-on body))))
#|
Validity checks can take the place of variable refs, looking like this:
x ==> (begin (if valid? (void) (error "detected letrec violation"))
             x)

The conversion for assignments is similar.

Our implementation will insert validity checks only where needed, and if none
are determined to be needed, it will not introduce the valid? flag. The
difficulty is, of course, in telling where the checks are needed. Consider:
|#
#;
(letrec ([x 0]
         [f (let ([g (lambda () x)])
              g)])
  <body>)
;; versus:
#;
(letrec ([x 0]
         [f (let ([g (lambda () x)])
              (h g))]) ;; where h is defined elsewhere
  <body>)
#|
In the first, the references to both g and x are safe, since the thunk is not
invoked. In the second, we don't know if h will invoke g, so we must check the
reference to x.

Here is our strategy; much more detail is in Sec. 2.3 of the paper on the
algorithm, "Fixing Letrec: A Faithful Yet Efficient Implementation of Scheme's
Recursive Binding Construct," by Waddell, Dybvig, and Sarkar.

Variables have three states: protected, unprotected, and protectable.  The
state is tracked via extra arguments to the recursion: a list of unprotected
variables, and a list of protectable variables. (Any in neither list are
considered protected.)  Here is how the state transitions work:

* All letrec-variables begin in the protectable state when we begin processing
  a RHS expression from the letrec that binds them.

* We move all protectable vars into the protected state when entering a lambda-
  expression.

* We move all protectable vars into the unprotected state when entering an
  unsafe context.  For our purposes, "unsafe context" means the operator or
  operands of a function (not primitive) application, and some RHS
  expressions in let- and letrec-expressions.

The input language is Lang5:

      <Prog> ::= (let () <Defs> <Exp>)

       <Exp> ::= (begin <NB-Exp> <NB-Exp>+)
               | <NB-Exp>

    <NB-Exp> ::= (quote <Lit>)
               | <Var>
               | (set! <Var> <Exp>)
               | (if <Exp> <Exp> <Exp>)
               | (let (<Decl>*) <Tagged-Exp>)
               | (letrec (<Decl>*) <Tagged-Exp>)
               | (lambda (<Var>*) <Tagged-Exp>)
               | (<Prim> <Exp>*)
               | (<Exp> <Exp>*)

<Tagged-Exp> ::= (tag (asgd <Var>*) (refd <Var>*) <Exp>)

      <Decl> ::= (<Var> <Exp>)

The output language is the same; the program structure still fits the grammar
of Lang5.
|#

;; In the below, a Flag is an identifier (i.e., symbol) representing a Boolean
;; valid? flag variable.

;; enforce-letrec-rule : Lang5:Prog -> Lang5:Prog
(define (enforce-letrec-rule prog)
  
  ;; elr : Exp Set[Id] Set[Id] Env[Id => Id] --> Exp Setof[Id] Setof[Id]
  ;; x is the expression to be processed; unprotected and protectable are
  ;; sets of letrec-bound variables; and flags is an env mapping letrec-bound
  ;; variables to their valid? flags.
  ;; This function produces three values:
  ;;   * the new expression
  ;;   * the set of all variables that were referenced/assigned unsafely (i.e.,
  ;;     while unprotected or protectable) in the expression
  ;;   * the set of vars that were referenced (for determining whether each
  ;;     letrec needs the flag generated).
  (define (elr x unprotected protectable flags)
    (match x
      [(list 'begin e es ...)
       (let-values ([(e* unsafe refd)
                     (map/union (curryr elr/nb unprotected protectable flags)
                                (cons e es))])
         (values `(begin ,@e*) unsafe refd))]
      [_ (elr/nb x unprotected protectable flags)]))
  (define (elr/nb x unprotected protectable flags)
    (match x
      [(list 'quote lit)
       (values x (seteq) (seteq))]
      [(? symbol? x)
       (if (or (set-member? unprotected x) (set-member? protectable x))
           (let ([flag/f (lookup x flags)])
             (if flag/f
                 (values (check-ref x flag/f)
                         (seteq x)
                         (seteq x flag/f))
                 (values x (seteq x) (seteq x))))
           (values x (seteq) (seteq x)))]
      [(list 'set! (? symbol? id) rhs)
       (let-values ([(rhs unsafe refd)
                     ;; Unlike in the paper, I am treating this RHS as unsafe;
                     ;; This is correct because of the example below labeled
                     ;; "Unsafe set!".
                     (elr rhs (set-union unprotected protectable)
                          (seteq)
                          flags)])
         (let ([flag/f (and (or (set-member? unprotected id)
                                (set-member? protectable id))
                            (lookup id flags))]
               [new-x `(set! ,id ,rhs)])
           (if flag/f
               (values (check-ref new-x flag/f)
                       unsafe
                       (set-add refd flag/f))
               (values new-x unsafe refd))))]
      ;;;;;
      [(list 'if test e1 e2)
       (let-values ([(ifbody unsafe refd)
                     (map/union (curryr elr unprotected protectable flags)
                                (list test e1 e2))])
         (values (cons 'if ifbody) unsafe refd))]
      ;;;;;
      [(list 'let (list (and (list (? symbol? Ls) Rs) decls)
                        ...)
             (list 'tag (list 'asgd asgd-ids ...) (list 'refd refd-ids ...)
                   body))
       ;; This case is more complicated:
       ;;   Process the body with all locally-bound vars protectable.
       ;;   For each locally-bound var that is unsafely ref'd in the body,
       ;;      process the RHS as unsafe.
       ;;   For each locally-bound var that is not, process the RHS as safe.
       (let*-values ([(body unsafe/body refd/body)
                      (elr body unprotected protectable flags)])
         (define (process-decl decl)
           (let ([L (first decl)][R (second decl)])
             (let-values ([(R unsafe/R refd/R)
                           (if (set-member? unsafe/body L)
                               ;; Mark the protectable vars unprotected;
                               ;; this RHS isn't safe:
                               (elr R (set-union unprotected protectable)
                                    (seteq)
                                    flags)
                               ;; Mark the protectable vars protected;
                               ;; they're not ref'd unsafely in the body:
                               (elr R unprotected (seteq) flags))])
               (values (list L R) unsafe/R refd/R))))
         (let-values ([(decls unsafe/decls refd/decls)
                       (map/union process-decl decls)])
           (values `(let ,decls
                      (tag (asgd ,@asgd-ids) (refd ,@refd-ids)
                           ,body))
                   (set-union unsafe/body unsafe/decls)
                   (set-union refd/body refd/decls))))]
      ;; The most complex case: letrec.  Here we must
      ;;   1: Process the body.
      ;;   2: Partition the RHS expressions into "unsafe" and "safe" ones.
      ;;      If the corresponding LHS variable is referenced unsafely
      ;;       (i.e., while unprotected or protectable), consider the RHS
      ;;       unsafe.
      ;;   3: Process all the unsafe RHS expressions with the outer protectable
      ;;       variables unprotected and the LHS variables protectable.
      ;;   4: Process all the remaining RHS expressions.
      ;; In both (3) and (4), insert validity checks for any LHS variable that
      ;; is referenced while unprotected or protectable.
      [(list 'letrec (list (and (list (? symbol? Ls) Rs) decls) ...)
             (list 'tag (list 'asgd asgd-ids ...) (list 'refd refd-ids ...)
                   body))
       (define Lset (list->seteq Ls))
       (define valid? (gensym 'valid?))
       (let-values ([(body unsafe/body refd/body)
                     (elr body unprotected (set-union protectable Lset)
                          flags)])
         (let ([flags (extend-env Ls (make-list (length Ls) valid?) flags)])
           (define (L-used-unsafely? decl unsafe-vars)
             (and (set-member? unsafe-vars (first decl)) #t))
           (define p&u (set-union unprotected protectable))
           (define p&Ls (set-union protectable Lset))
           (let ()
             ; Decl Listof[decl]^2
             ;;  -> (values Decl Set[Id] Set[Id] Listof[decl] Listof[decl])
             ; process an unsafe RHS (decl), given also the other unsafe decls
             ; and the safe decls; return the resulting decl and the sets of
             ; unsafe and safe decls that result (marking unsafe any RHSs whose
             ; names are referenced in this RHS)
             (define (process-unsafe-decl decl unsafe-decls safe-decls)
               (let*-values ([(R unsafe/R refd/R)
                              (elr (second decl) p&u Lset flags)]
                             [(unsafe-decls safe-decls)
                              (for/fold ([unsafe-decls unsafe-decls]
                                         [new-safe-decls '()])
                                ([safe-decl safe-decls])
                                (if (set-member? refd/R (first safe-decl))
                                    (values (cons safe-decl unsafe-decls)
                                            new-safe-decls)
                                    (values unsafe-decls
                                            (cons safe-decl
                                                  new-safe-decls))))])
                 (values (list (first decl) R)
                         unsafe/R refd/R
                         unsafe-decls safe-decls)))
             
             ;; process-all-decls/unsafe : Listof[decl]^3
             ;;   -> (values Listof[decl] Set[Id] Set[Id])
             ;; Process the decls -- first the unsafe ones, then the safe ones,
             ;; producing a list of all decls that have been processed, and the
             ;; sets of all unsafely-referenced vars and all referenced vars.
             ;; unsafe : unsafe decls remaining to be processed (including any
             ;;    which have been reconsidered as unsafe by references found
             ;;    in processing other unsafe decls' RHSs)
             ;; safe : safe decls remaining to be processed.
             ;; processed : list of all decls that have been processed so far.
             (define (process-all-decls/unsafe unsafe-decls safe-decls
                                               processed-decls
                                               unsafe/R* refd/R*)
               (cond
                 [(empty? unsafe-decls)
                  (process-all-decls/safe safe-decls
                                          processed-decls
                                          unsafe/R* refd/R*)]
                 [else
                  (let-values ([(new-first unsafe/R refd/R
                                           unsafe-decls safe-decls)
                                (process-unsafe-decl (first unsafe-decls)
                                                     (rest unsafe-decls)
                                                     safe-decls)])
                    (process-all-decls/unsafe unsafe-decls safe-decls
                                              (cons new-first processed-decls)
                                              (set-union unsafe/R unsafe/R*)
                                              (set-union refd/R refd/R*)))]))
             ;; Listof[Decl]^2 Set[Id]^2 -> (Listof[Decl] Set[Id]^2)
             ;; process the RHSs of the safe-decls; processed accumulates the
             ;; processed decls, and unsafe/R* and refd/R* are the sets of vars
             ;; unsafely-referenced and referenced in the RHSs of all decls of
             ;; this letrec.
             (define (process-all-decls/safe safe-decls processed
                                             unsafe/R* refd/R*)
               (define (elr-rhs decl)
                 (let ([L (first decl)]
                       [R (second decl)])
                   (let-values ([(R unsafe/R refd/R)
                                 (elr R unprotected p&Ls flags)])
                     (values (list L R) unsafe/R refd/R))))
               (let-values ([(processed-safe-decls unsafe/safe-Rs refd/safe-Rs)
                             (map/union elr-rhs safe-decls)])
                 (values (append processed-safe-decls processed)
                         (set-union unsafe/safe-Rs unsafe/R*)
                         (set-union refd/safe-Rs refd/R*))))
             
             (define-values (unsafe-decls safe-decls)
               (partition (curryr L-used-unsafely? unsafe/body) decls))
             
             (let*-values ([(processed-decls unsafe/R* refd/R*)
                            (process-all-decls/unsafe unsafe-decls safe-decls
                                                      empty
                                                      (seteq) (seteq))])
               (values (if (set-member? refd/R* valid?)
                           `(let ([,valid? '#f])
                              (tag (asgd) (refd ,valid?)
                                   (letrec ,processed-decls
                                     (tag (asgd ,@asgd-ids) (refd ,@refd-ids)
                                          (begin (set! ,valid? '#t)
                                                 ,body)))))
                           `(letrec ,processed-decls
                              (tag (asgd ,@asgd-ids) (refd ,@refd-ids) ,body)))
                       (set-union unsafe/body unsafe/R*)
                       (set-remove (set-union refd/body refd/R*)
                                   valid?))))))]
      
      [(list 'lambda (list (? symbol? formals) ...)
             (list 'tag (list 'asgd asgd-ids ...) (list 'refd refd-ids ...)
                   body))
       (let-values ([(body unsafe flags-refd)
                     (elr body unprotected (seteq) flags)])
         (values `(lambda ,formals
                    (tag (asgd ,@asgd-ids) (refd ,@refd-ids) ,body))
                 unsafe
                 flags-refd))]
      [(list 'lambda anything-else ...)
       (error 'enforce-letrec-rule
              "expected Lang5 program, but encountered ~s in input program ~s"
              x prog)]
      [(list (? primitive? prim) args ...)
       (if (effect-free-prim? prim)
           (let-values ([(args unsafe refd)
                         (map/union (curryr elr unprotected protectable flags)
                                    args)])
             (values (cons prim args) unsafe refd))
           (let-values ([(args unsafe refd)
                         (map/union (curryr elr
                                            (set-union unprotected protectable)
                                            (seteq)
                                            flags)
                                    args)])
             (values (cons prim args) unsafe refd)))]
      [(list proc args ...)
       (map/union (curryr elr
                          (set-union unprotected protectable)
                          (seteq)
                          flags)
                  (cons proc args))]
      [_
       (error 'enforce-letrec-rule
              "expected Lang5 program, but encountered ~s in input program ~s"
              x prog)]))
  
  ;; map/union :
  ;;    (W X Y Z -> W' Seteq[Id] Seteq[Id]) Listof[W]
  ;;    --> Listof[W'] Seteq[Id] Seteq[Id]
  ;; map f over xs, returning the list of all first return values and the
  ;; unions of all second and of all third return values.
  (define (map/union f xs)
    (for/fold ([new-xs '()][ids1 (seteq)][ids2 (seteq)]) ([x (reverse xs)])
      (let-values ([(new-x s1 s2) (f x)])
        (values (cons new-x new-xs)
                (set-union ids1 s1)
                (set-union ids2 s2)))))

  (let-values ([(e unsafe flags-refd)
                (elr (unwrap prog) (seteq) (seteq) (empty-env))])
    (wrap ,e)))


;; check-ref : Exp Flag -> Expr
;; wrap a check around the given variable reference or assignment, using the
;; given flag.
(define (check-ref e valid?)
  `(begin (if ,valid?
              (void)
              (error ,(string->nested-primapps "detected letrec violation")))
          ,e))



;; wrap: wrap an <Exp> of Lang5 in the (let () ...) form required by the
;; language.
(define-syntax-rule (wrap e)
  `(let ()
     (begin
       (define-syntax tag
         (syntax-rules (asgd refd)
           [(_ (asgd SVar (... ...)) (refd RVar (... ...)) Expr)
            Expr])))
     e))

;; unwrap : Lang5:Prog -> Lang5:Exp
(define (unwrap prog)
  (match prog
    [(list 'let '() stx-def e) e]))

(define pass6 enforce-letrec-rule)
(define this-pass pass6)

(module+ test
  (require (rename-in racket [error sys-err]))
  
  (define (error ls)
    (sys-err (list->string ls)))
  (define-namespace-anchor a)
  (define ns (namespace-anchor->namespace a))
  (compiler-tests/aeq enforce-letrec-rule
    lang5
    (,(wrap '5) ,(wrap '5))
    ; Test trivial let and letrec:
    (,(wrap (let () (tag (asgd) (refd) '5)))
     ,(wrap (let () (tag (asgd) (refd) '5))))
    (,(wrap (letrec () (tag (asgd) (refd) '5)))
     ,(wrap (letrec () (tag (asgd) (refd) '5))))
    ; simple tests for let- and lambda-bound vars:
    (,(wrap (let ([x '1]) x))
     ,(wrap (let ([x '1]) x)))
    (,(wrap (let ([x '1]) (cons x x)))
     ,(wrap (let ([x '1]) (cons x x))))
    (,(wrap (let ([x '1]) (begin '1 x '2 x '3 x)))
     ,(wrap (let ([x '1]) (begin '1 x '2 x '3 x))))
    (,(wrap (let ([x '1]) (+ x (begin (set! x '2) x))))
     ,(wrap (let ([x '1]) (+ x (begin (set! x '2) x)))))
    (,(wrap (lambda (x y) (tag (asgd) (refd) (+ (* x x) (* y y)))))
     ,(wrap (lambda (x y) (tag (asgd) (refd) (+ (* x x) (* y y))))))
    (,(wrap (lambda (x y)
              (tag (asgd) (refd)
                   (begin (set! x (* x x)) (set! y (* y y)) (+ x y)))))
     ,(wrap (lambda (x y)
              (tag (asgd) (refd)
                   (begin (set! x (* x x)) (set! y (* y y)) (+ x y))))))
    (,(wrap (let ([f (lambda (x)
                       (tag (asgd) (refd) (+ (* '2 x) '1)))])
              (f '5)))
     ,(wrap (let ([f (lambda (x)
                       (tag (asgd) (refd) (+ (* '2 x) '1)))])
              (f '5))))
    (,(wrap (let ([a '5][f (lambda (x)
                             (tag (asgd) (refd)
                                  (+ (* '2 x) '1)))]) (f a)))
     ,(wrap (let ([a '5][f (lambda (x)
                             (tag (asgd) (refd) (+ (* '2 x) '1)))])
              (f a))))
    ; Test for unsafeness of a set!'s RHS:
    (,(wrap (let ([f '#f])
              (tag (asgd f) (refd f)
                   (letrec ([x (begin (set! f (lambda ()
                                                (tag (asgd) (refd)
                                                     (+ '1 y))))
                                      (f))]
                            [y '0])
                     (tag (asgd) (refd x y)
                          (cons x (cons y '())))))))
     ,(wrap (let ([f '#f])
              (tag (asgd f) (refd f)
                   (let ([valid?0 '#f])
                     (tag (asgd) (refd valid?0)
                          (letrec ([y '0]
                                   [x (begin 
                                        (set! f
                                              (lambda ()
                                                (tag (asgd) (refd)
                                                     (+ '1
                                                        ,(check-ref 'y
                                                                    'valid?0)))))
                                        (f))])
                            (tag (asgd) (refd x y)
                                 (begin (set! valid?0 '#t)
                                        (cons x (cons y '())))))))))))
    ; Test for unsafeness of a vector-set! R-value:
    (,(wrap (let ([v (make-vector '1)])
              (tag (asgd) (refd v)
                   (letrec ([x (begin (vector-set! v '0 (lambda ()
                                                          (tag (asgd) (refd)
                                                               (+ '1 y))))
                                      ((vector-ref v '0)))]
                            [y '1])
                     (tag (asgd) (refd x y)
                          (cons x (cons y '())))))))
     ,(wrap (let ([v (make-vector '1)])
              (tag (asgd) (refd v)
                   (let ([valid?0 '#f])
                     (tag (asgd) (refd valid?0)
                          (letrec ([y '1]
                                   [x (begin
                                        (vector-set!
                                         v '0
                                         (lambda ()
                                           (tag (asgd) (refd)
                                                (+ '1
                                                   ,(check-ref 'y
                                                               'valid?0)))))
                                        ((vector-ref v '0)))])
                            (tag (asgd) (refd x y)
                                 (begin (set! valid?0 '#t)
                                        (cons x (cons y '())))))))))))
    ; Ordinary factorial test -- all refs are OK:
    (,(wrap (letrec ([! (lambda (n)
                          (tag (asgd) (refd n)
                               (if (zero? n) '1 (* n (! (sub1 n))))))])
              (tag (asgd) (refd !) (! '5))))
     ,(wrap (letrec ([! (lambda (n)
                          (tag (asgd) (refd n)
                               (if (zero? n) '1
                                   (* n (! (sub1 n))))))])
              (tag (asgd) (refd !) (! '5)))))
    ; These next 2 tests are for how an unsafe reference in a letrec RHS,
    ; versus a safe one, affects compilation:
    (,(wrap (letrec ([x (letrec ([g (lambda ()
                                      (tag (asgd) (refd) (h)))] ; safe h ref
                                 [h (lambda ()
                                      (tag (asgd) (refd) y))])
                          ; unsafe in body -> g's RHS is unsafe
                          ; -> h's RHS is unsafe
                          ; -> the ref to y must be checked.
                          (tag (asgd) (refd g h) (g)))]
                     [y '2])
              (tag (asgd) (refd x y)
                   (cons x (cons y '())))))
     ,(wrap (let ([valid?0 '#f])
              (tag (asgd) (refd valid?0)
                   (letrec ([y '2]
                            [x (letrec ([h (lambda ()
                                             (tag (asgd) (refd)
                                                  ,(check-ref 'y 'valid?0)))]
                                        [g (lambda ()
                                             (tag (asgd) (refd) (h)))])
                                 (tag (asgd) (refd g h) (g)))])
                     (tag (asgd) (refd x y)
                          (begin (set! valid?0 '#t)
                                 (cons x (cons y '())))))))))
    (,(wrap (letrec ([x (letrec ([g (lambda ()
                                      (tag (asgd) (refd) '0))]
                                 [h (lambda ()
                                      (tag (asgd) (refd) y))])
                          (tag (asgd) (refd g h)
                               (lambda ()
                                 (tag (asgd) (refd)
                                      (cons g (cons h '()))))))]
                     [y '2])
              (tag (asgd) (refd x y)
                   (let ([f1 (car (x))][f2 (cadr (x))])
                     (cons (f1) (cons (f2) (cons y '())))))))
     ,(wrap (letrec ([y '2]
                     [x (letrec ([g (lambda ()
                                      (tag (asgd) (refd) '0))]
                                 [h (lambda ()
                                      (tag (asgd) (refd) y))])
                          (tag (asgd) (refd g h)
                               (lambda ()
                                 (tag (asgd) (refd)
                                      (cons g (cons h '()))))))])
              (tag (asgd) (refd x y)
                   (let ([f1 (car (x))][f2 (cadr (x))])
                     (cons (f1) (cons (f2) (cons y '()))))))))

    ) ;; end compiler-tests/aeq?
  
  )

;; Unsafe set!:
#;(let ([f '#f])
    (tag (asgd f) (refd f)
         (letrec ([x (begin (set! f (lambda () (tag (asgd) (refd y) (+ '1 y))))
                            (f))]
                  [y '0])
           (tag (asgd) (refd x y)
                (list x y)))))
;; Safe:
#;(letrec ([x '10]
           [f (let ([h (letrec ([g (lambda (n)
                                     (if (<= n x)
                                         n
                                         (+ n (g (- n '1)))))])
                         (lambda (c) (g (+ c '10))))])
                (lambda () (h x)))])
    (f))

#|
If the body of a let or letrec contains an unsafe reference to a locally-bound
variable, then the RHS of that variable's binding is unsafe.
(NOTE: it's conceivable we could do something like this with set!, but seems
like it would be a lot of work (if not impossible) to determine that a set! is
certainly safe.)
If the body of a let or letrec contains only safe references to a locally-bound
variable, then the RHS of that variable's binding is safe.
Proof by induction on the number of let/letrec forms contained in the RHS of a
decl?
|#

