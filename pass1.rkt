#lang racket

(require "support/env.rkt"
         "support/helpers.rkt"
         )

(provide pass1 rename-vars/verify-legal)

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

; Input language:
; <Exp>  ::= <Const>
;          | (quote <Lit>)
;          | <Var>
;          | (set! <Var> <Exp>)
;          | (when <Exp> <Exp>)
;          | (unless <Exp> <Exp>)
;          | (if <Exp> <Exp> <Exp>)
;          | (begin <Exp> <Exp>*)
;          | (let (<Decl>*) <Exp> <Exp>*)
;          | (letrec (<Decl>*) <Exp> <Exp>*)
;          | (lambda (<Var>*) <Exp> <Exp>*)
;          | (<Prim> <Exp>*)
;          | (<Exp> <Exp>*)
; <Decl> ::= (<Var> <Exp>)





;;; Pass 1: rename-vars/verify-legal
;
; Non-local helpers required: gen-symbol, set?, user-primitive?
;
; (Modified from the original version given with assignment 1.)
;
; Input language:
;
; <Exp>  ::= <Const>
;          | (quote <Lit>)
;          | <Var>
;          | (set! <Var> <Exp>)
;          | (if <Exp> <Exp>)
;          | (if <Exp> <Exp> <Exp>)
;          | (begin <Exp> <Exp>*)
;          | (let (<Decl>*) <Exp> <Exp>*)
;          | (letrec (<Decl>*) <Exp> <Exp>*)
;          | (lambda (<Var>*) <Exp> <Exp>*)
;          | (<Prim> <Exp>*)
;          | (<Exp> <Exp>*)
; <Decl> ::= (<Var> <Exp>)
;
; The list of acceptable primitives (<Prim>) is described above in the
; definition of list-of-user-primitives; constants (<Const>), recognized by the
; procedure constant?, include the empty list, characters, booleans, and
; integers.
;
; This pass ensures that an input program is legitimate (insofar as it matches
; the grammar and contains no references or assignments to unbound identifiers)
; and renames all variables so that each variable is uniquely named.

(define (rename-vars/verify-legal expr)
  ;; rv/vl : S-expr Env[Sym => Sym] -> Lang1
  ;; Replaces all identifiers so every variable is uniquely named within the
  ;; program, and verifies that the form of the program is valid.  env maps
  ;; ids to renamed ids.
  (define (rv/vl x env)
    (match x
      [(? constant? x) x]
      [(list 'quote x) (list 'quote x)]
      [(? symbol? x)
       (or (lookup x env)
           (raise (make-exn:fail:contract:variable
                   (format "reference to unbound identifier ~s in ~s"
                           x expr)
                   (current-continuation-marks)
                   x)))]
      [(list 'set! (? symbol? lhs) rhs)
       `(set! ,(or (lookup lhs env)
                   (raise (make-exn:fail:contract:variable
                           (format
                            "assignment to unbound identifier ~s in ~s"
                            lhs expr)
                           (current-continuation-marks)
                           lhs)))
              ,(rv/vl rhs env))]
      [(list 'when test result)
       `(when ,(rv/vl test env) ,(rv/vl result env))]
      [(list 'unless test result)
       `(unless ,(rv/vl test env) ,(rv/vl result env))]
      [(list 'if test e1 e2)
       `(if ,(rv/vl test env) ,(rv/vl e1 env) ,(rv/vl e2 env))]
      [(list 'begin e1 e* ...)
       `(begin ,(rv/vl e1 env) ,@(map (curryr rv/vl env) e*))]
      [(list 'let (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       (let* ([new-vars (map gensym lhs)]
              [body-env (extend-env lhs new-vars env)])
         `(let ,(map list new-vars (map (curryr rv/vl env) rhs))
            ,(rv/vl e1 body-env)
            ,@(map (curryr rv/vl body-env) e*)))]
      [(list 'letrec (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       (let* ([new-vars (map gensym lhs)]
              [new-env (extend-env lhs new-vars env)])
         `(letrec ,(map list new-vars (map (curryr rv/vl new-env) rhs))
            ,(rv/vl e1 new-env)
            ,@(map (curryr rv/vl new-env) e*)))]
      [(list 'lambda (list (? symbol? formals) ...) e1 e* ...)
       (let* ([new-formals (map gensym formals)]
              [env (extend-env formals new-formals env)])
         `(lambda ,new-formals
            ,(rv/vl e1 env)
            ,@(map (curryr rv/vl env) e*)))]
      [(list (? primitive? prim) args ...)
       `(,prim ,@(map (curryr rv/vl env) args))]
      [(list proc args ...)
       (map (curryr rv/vl env) `(,proc ,@args))]
      [something-else
       (raise (make-exn:fail
               (if (eq? something-else expr)
                   (format "malformed input program ~s" something-else)
                   (format "malformed expr ~s in input program:\n~s"
                           something-else expr))
               (current-continuation-marks)))]))
  (rv/vl expr (empty-env)))

(define pass1 rename-vars/verify-legal)
(define this-pass pass1)

(module+ test
  
  (compiler-tests/aeq rename-vars/verify-legal
    (5                     5)
    ((if #t 5 6)           (if #t 5 6))
    ((if #t (if #f 7 8) 6) (if #t (if #f 7 8) 6))
    ((when #f 42)          (when #f 42))
    ((unless #f 42)        (unless #f 42))
    ((let ([x 0])
       (set! x (add1 x))
       x)
     (let ([x 0])
       (set! x (add1 x))
       x))
    ((let ([x 0])
       (set! x (add1 x))
       x)
     (let ([x 0])
       (set! x (add1 x))
       x))
    ((let ([a 1][b 2]) (begin a b))
     (let ([a 1][b 2]) (begin a b)))
    ((let ([a 1]) a)
     (let ([a 1]) a))
    ((let ([a 1][b 2]) (set! b 4) (+ a b))
     (let ([a 1][b 2]) (set! b 4) (+ a b)))
    ((letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1))
     (letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1)))
    ((let ([! (void)])
       (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
       (+ (! 5) 1))
     (let ([! (void)])
       (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
       (+ (! 5) 1)))
    )
  
  )
