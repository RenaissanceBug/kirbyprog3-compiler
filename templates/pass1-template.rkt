#lang racket

(require "support/env.rkt" "support/helpers.rkt")

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

;;; Pass 1: rename-vars/verify-legal
;
; Input and output language, Lang1:
;
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
;
; The list of acceptable primitives (<Prim>) is described above in the
; definition of list-of-user-primitives; constants (<Const>), recognized by the
; procedure constant?, include the empty list, characters, booleans, and
; integers.
;
; This pass ensures that an input program is legitimate (insofar as it matches
; the grammar and contains no references OR assignments to unbound identifiers)
; and renames all variables so that each variable is uniquely named.

;; rename-vars/verify-legal : Lang1 -> Lang1
;; Replaces all identifiers so every variable is uniquely named within the
;; program, and verifies that the form of the program is valid, per the above.
(define (rename-vars/verify-legal expr)
  ;; rv/vl : S-expr Env[Sym => Sym] -> Lang1
  ;; Replaces all identifiers so every variable is uniquely named within the
  ;; program, and verifies that the form of the program is valid.  env maps
  ;; ids to renamed ids.
  (define (rv/vl x env)
    (match x
      #;[(? constant? x) ...]
      #;[(list 'quote x) ...]
      #;[(? symbol? x)
       ...]
      #;[(list 'set! (? symbol? lhs) rhs)
       ...]
      #;[(list 'when test result)
       ...]
      #;[(list 'unless test result)
       ...]
      #;[(list 'if test e1 e2)
       ...]
      #;[(list 'begin e1 e* ...)
       ...]
      #;[(list 'let (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       ...]
      #;[(list 'letrec (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       ...]
      #;[(list 'lambda (list (? symbol? formals) ...) e1 e* ...)
       ...]
      #;[(list (? primitive? prim) args ...)
       ...]
      #;[(list proc args ...)
       ...]
      [something-else
       (raise (make-exn:fail
               (if (eq? something-else expr)
                   (format "malformed input program ~s" something-else)
                   (format "malformed expr ~s in input program:\n~s"
                           something-else expr))
               (current-continuation-marks)))]))
  (rv/vl expr (empty-env)))

;; alpha-equivalent? : Lang1 Lang1 -> Lang1
;; determines whether the two given programs are equivalent up to renaming
;; of bound variables.
(define (alpha-equivalent? e1 e2)
  ;; Lang1 Lang1 Env[Sym => Sym] -> Boolean
  ;; env maps bound variables of e1 to bound variables of e2.
  (define (aeq? e1 e2 env)
    (match e1
      #;[(? constant? x) ...]
      #;[(list 'quote x) ...]
      #;[(? symbol? x)
       ...]
      #;[(list 'set! (? symbol? lhs) rhs)
       ...]
      #;[(list 'when test result)
       ...]
      #;[(list 'unless test result)
       ...]
      #;[(list 'if test e1 e2)
       ...]
      #;[(list 'begin e1 e* ...)
       ...]
      #;[(list 'let (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       ...]
      #;[(list 'letrec (list (list (? symbol? lhs) rhs) ...) e1 e* ...)
       ...]
      #;[(list 'lambda (list (? symbol? formals) ...) e1 e* ...)
       ...]
      #;[(list (? primitive? prim) args ...)
       ...]
      #;[(list proc args ...)
       ...]
      [something-else #f]))
  (aeq? e1 e2 (empty-env)))

;; Aliases:
(define pass1 rename-vars/verify-legal)
(define this-pass pass1)

;; Test code follows.

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
       (set! x (add1 5))
       x))
    ((let ([x 0])
       (set! x (add1 x))
       x)
     (let ([x 0])
       (begin (set! x (add1 x))
              x)))
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