#lang racket

(require "support/helpers.rkt")

(provide pass5 uncover-assigned/referenced)

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

#|
Pass 4: uncover-assigned/referenced : Lang4 -> Lang5

Input language, Lang4:

    <Exp> ::= (begin <NB-Exp> <NB-Exp>+)
           | <NB-Exp>

 <NB-Exp> ::= (quote <Lit>)
           | <Var>
           | (set! <Var> <Exp>)
           | (if <Exp> <Exp> <Exp>)
           | (let (<Decl>*) <Exp>)
           | (letrec (<Decl>*) <Exp>)
           | (lambda (<Var>*) <Exp>)
           | (<Prim> <Exp>*)
           | (<Exp> <Exp>*)

  <Decl> ::= (<Var> <Exp>)

This pass tags all let, letrec, and lambda expressions that bind variables
that will later be modified by set!, and all that bind variables that are
referenced.

In doing so it modifies the let, letrec, and lambda variants of <NB-Exp>:

<Tagged-Exp> ::= (tag (asgd <Var>*) (refd <Var>*) <Exp>)
<NB-Exp> ::= (let (<Decl>*) <Tagged-Exp>)
           | (letrec (<Decl>*) <Tagged-Exp>)
           | (lambda (<Var>*) <Tagged-Exp>)

When finished, the pass wraps the result in a syntax definition that strips
all but the <Exp> from a <Tagged-exp> when the pass output is evaluated.
This requires one more change to the output grammar:

<Prog> ::= (let () <Defs> <Exp>)

<Defs> hereafter (i.e., in this and future passes) will always refer to a
begin-expr containing definitions necessary to execute output programs.)

So, here is the entire output language, Lang5:

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
|#

;; uncover-assigned/referenced : Lang4:Exp -> Lang5:Exp
;; As described above.
(define (uncover-assigned/referenced expr)
  ;; usr : Lang4:Exp -> Lang5:Exp Set[Id] Set[Id]
  ;; produce the Lang5 expression equivalent to x, and the sets of
  ;; assigned and referenced variables.
  (define (uar x)
    (match x
      [(list 'quote lit)
       (values x (seteq) (seteq))]
      [(? symbol? id)
       (values x (seteq) (seteq id))]
      [(list 'set! (? symbol? id) rhs)
       (let-values ([(rhs asgd refd) (uar rhs)])
         (values `(set! ,id ,rhs) (set-add asgd id) refd))]
      [(list 'if test e1 e2)
       (let-values ([(test t-asgd t-refd) (uar test)]
                    [(e1 e1-asgd e1-refd) (uar e1)]
                    [(e2 e2-asgd e2-refd) (uar e2)])
         (values `(if ,test ,e1 ,e2)
                 (set-union t-asgd e1-asgd e2-asgd)
                 (set-union t-refd e1-refd e2-refd)))]
      [(list 'begin e* ...)
       (let-values ([(e* asgd refd) (map-uar e*)])
         (values (cons 'begin e*) asgd refd))]
      [(list 'let (list (list (? symbol? Ls) Rs) ...) body)
       (let-values ([(Rs R-asgd R-refd) (map-uar Rs)]
                    [(body b-asgd b-refd) (uar body)])
         (let ([L-set (list->seteq Ls)])
           (values `(let ,(map list Ls Rs)
                      (tag (asgd ,@(∩-list L-set b-asgd))
                           (refd ,@(∩-list L-set b-refd))
                           ,body))
                   (set-union R-asgd (set-subtract b-asgd L-set))
                   (set-union R-refd (set-subtract b-refd L-set)))))]
      ; The processing for letrec is similar to that for let, except
      ; that assigned vars occurring in binding expressions are
      ; matched with the letrec's bindings where possible, not
      ; automatically passed on to some enclosing level.
      [(list 'letrec (list (list (? symbol? Ls) Rs) ...) body)
       (let-values ([(Rs R-asgd R-refd) (map-uar Rs)]
                    [(body b-asgd b-refd) (uar body)])
         (let ([L-set (list->seteq Ls)]
               [asgd (set-union R-asgd b-asgd)]
               [refd (set-union R-refd b-refd)])
           (values `(letrec ,(map list Ls Rs)
                      (tag (asgd ,@(∩-list L-set asgd))
                           (refd ,@(∩-list L-set refd))
                           ,body))
                   (set-subtract asgd L-set)
                   (set-subtract refd L-set))))]
      [(list 'lambda (list (? symbol? formals) ...) body)
       (let-values ([(body asgd refd) (uar body)])
         (let ([formal-set (list->seteq formals)])
           (values `(lambda ,formals
                      (tag (asgd ,@(∩-list formal-set asgd))
                           (refd ,@(∩-list formal-set refd))
                           ,body))
                   (set-subtract asgd formal-set)
                   (set-subtract refd formal-set))))]
      [(list (? primitive? prim) args ...)
       (let-values ([(args asgd refd) (map-uar args)])
         (values (cons prim args) asgd refd))]
      [(list proc args ...)
       (let-values ([(proc p-asgd p-refd) (uar proc)]
                    [(args a-asgd a-refd) (map-uar args)])
         (values (cons proc args)
                 (set-union p-asgd a-asgd)
                 (set-union p-refd a-refd)))]
      [_
       (error 'uncover-assigned/referenced
              "expected Lang4 expr, but encountered ~s in input program ~s"
              x expr)]))
  
  ;; ∩-list : Set[Id] Set[Id] -> List[Id]
  ;; produces the intersection of the two sets as a list
  (define (∩-list set1 set2) (set->list (set-intersect set1 set2)))
  
  ;; Listof[Lang4:Exp] -> Listof[Lang5:Exp] Set[Id] Set[Id]
  ;; calls uar on each expr in exprs, and produces the list of corresponding
  ;; Lang5 exprs and the unions of all asg'd and ref'd vars in exprs.
  (define (map-uar exprs)
    (for/fold ([exprs '()][asgd (seteq)][refd (seteq)])
      ([e (reverse exprs)])
      (let-values ([(e e-asgd e-refd) (uar e)])
        (values (cons e exprs)
                (set-union e-asgd asgd)
                (set-union e-refd refd)))))
  
  (wrap
   ,(let-values ([(new-expr assigned-vars referenced-vars) (uar expr)])
      new-expr)))

(define pass5 uncover-assigned/referenced)
(define this-pass pass5)

(define-syntax-rule (wrap e)
  `(let ()
     (begin
       (define-syntax tag
         (syntax-rules (asgd refd)
           [(_ (asgd SVar (... ...)) (refd RVar (... ...)) Expr)
            Expr])))
     e))


(module+ test
  (compiler-tests/equal? uncover-assigned/referenced
    ('5                         ,(wrap '5))
    ('#f                        ,(wrap '#f))
    ((if '#t '5 '6)             ,(wrap (if '#t '5 '6)))
    ((if '#t (if '#f '7 '8) '6) ,(wrap (if '#t (if '#f '7 '8) '6)))
    (      (let ([x '0])
             (begin (set! x (add1 x)) x))
           ,(wrap (let ([x '0])
                    (tag (asgd x) (refd x)
                         (begin (set! x (add1 x)) x)))))
    ((begin '1 '2 '3)
     ,(wrap (begin '1 '2 '3)))

    ((cons '5 (cons '6 (cons '7 (cons '8 '()))))
     ,(wrap (cons '5 (cons '6 (cons '7 (cons '8 '()))))))

    (       (let ([a '1][b '2])                        (begin a b a))
     ,(wrap (let ([a '1][b '2]) (tag (asgd) (refd a b) (begin a b a)))))

    (       (let ([a '1])                      (set! a '1))
     ,(wrap (let ([a '1]) (tag (asgd a) (refd) (set! a '1)))))

    ((let ([a '1][b '2]) (begin (set! b '4) (+ a b)))
     ,(wrap (let ([a '1][b '2])
              (tag (asgd b) (refd a b) (begin (set! b '4) (+ a b))))))

    ((letrec ([! (lambda (n) (if (= n '0) '1 (* n (! (- n '1)))))])
       (+ (! '5) '1))
     ,(wrap
       (letrec ([! (lambda (n)
                     (tag (asgd) (refd n)
                          (if (= n '0) '1 (* n (! (- n '1))))))])
         (tag (asgd) (refd !) (+ (! '5) '1)))))
    ((letrec ([f (lambda (n) (f n))])
       (begin (set! f (lambda (n) (+ '1 n)))
              (set! f (lambda (n) (+ '2 n)))
              (f '5)))
     ,(wrap
       (letrec ([f (lambda (n) (tag (asgd) (refd n) (f n)))])
         (tag (asgd f) (refd f)
              (begin (set! f (lambda (n) (tag (asgd) (refd n)
                                              (+ '1 n))))
                     (set! f (lambda (n) (tag (asgd) (refd n)
                                              (+ '2 n))))
                     (f '5))))))
    ((let ([! (void)][x '5])
       (begin (set! ! (lambda (n) (if (= n '0) '1 (* n (! (- n '1))))))
              (set! x (+ '1 x))
              (! x)))
     ,(wrap
       (let ([! (void)][x '5])
         (tag (asgd x !) (refd x !)
              (begin (set! ! (lambda (n)
                               (tag (asgd) (refd n)
                                    (if (= n '0) '1 (* n (! (- n '1)))))))
                     (set! x (+ '1 x))
                     (! x))))))
    ((let ([next! (let ([ctr '0])
                    (lambda ()
                      (begin (set! ctr (add1 ctr)) ctr)))])
       (let ([a (next!)])
         (let ([b (next!)])
           (cons a (cons b (cons (next!) '()))))))
     ,(wrap
       (let ([next! (let ([ctr '0])
                      (tag (asgd ctr) (refd ctr)
                           (lambda ()
                             (tag (asgd) (refd)
                                  (begin (set! ctr (add1 ctr)) ctr)))))])
         (tag (asgd) (refd next!)
              (let ([a (next!)])
                (tag (asgd) (refd a)
                     (let ([b (next!)])
                       (tag (asgd) (refd b)
                            (cons a (cons b (cons (next!) '())))))))))))
    ))
