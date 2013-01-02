#lang racket

(require "support/helpers.rkt")

(provide pass2 remove-implicit-begin/when/unless)

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

#|
Pass 2: remove-implicit-begin/when/unless

Input language is Lang1, as defined in Pass 1:

<Exp>  ::= <Const>
         | (quote <Lit>)
         | <Var>
         | (set! <Var> <Exp>)
         | (when <Exp> <Exp>)              <-- removed in Lang2
         | (unless <Exp> <Exp>)            <-- removed in Lang2
         | (if <Exp> <Exp> <Exp>)
         | (begin <Exp> <Exp>*)
         | (let (<Decl>*) <Exp> <Exp>*)    <-- changed in Lang2
         | (letrec (<Decl>*) <Exp> <Exp>*) <-- changed in Lang2
         | (lambda (<Var>*) <Exp> <Exp>*)  <-- changed in Lang2
         | (<Prim> <Exp>*)
         | (<Exp> <Exp>*)
<Decl> ::= (<Var> <Exp>)

This pass adds explicit (begin ...) wrappings around all expressions where
the (begin ...) is implied, and converts every when- and unless-expression
into an if-expression with a (void) third sub-expression (i.e., (void) for
the "else" case).  It should NOT add a (begin ...) where a let/letrec/λ has
only one body expression.

Output language, Lang2:

<Exp>  ::= <Const>
         | (quote <Lit>)
         | <Var>
         | (set! <Var> <Exp>)
         | (if <Exp> <Exp> <Exp>)
         | (begin <Exp> <Exp>*)
         | (let (<Decl>*) <Exp>)
         | (letrec (<Decl>*) <Exp>)
         | (lambda (<Var>*) <Exp>)
         | (<Prim> <Exp>*)
         | (<Exp> <Exp>*)
<Decl> ::= (<Var> <Exp>)

|#

;; remove-implicit-begin/when/unless : Lang1 -> Lang2
(define (remove-implicit-begin/when/unless expr)
  ;; simplify : Lang1 -> Lang2
  ;; main recursive helper, named for brevity
  (define (simplify x)
    (match x
      [(? constant? c)   x]
      [(list 'quote lit) x]
      [(? symbol? id)    x]
      [(list 'set! (? symbol? lhs) rhs)
       `(set! ,lhs ,(simplify rhs))]
      [(list 'when test result)
       `(if ,(simplify test) ,(simplify result) (void))]
      [(list 'unless test result)
       `(if (not ,(simplify test)) ,(simplify result) (void))]
      [(list 'if test e1 e2)
       `(if ,(simplify test) ,(simplify e1) ,(simplify e2))]
      [(list 'begin e1 e* ...)
       `(begin ,(simplify e1) ,@(map simplify e*))]
      [(list 'let (list (list (? symbol? lhs) rhs) ...) b bs ...)
       `(let ,(map simplify-decl lhs rhs)
          ,(simplify/maybe-wrap b bs))]
      [(list 'letrec (list (list (? symbol? lhs) rhs) ...) b bs ...)
       `(letrec ,(map simplify-decl lhs rhs)
          ,(simplify/maybe-wrap b bs))]
      [(list 'lambda (list (? symbol? formals) ...) b bs ...)
       `(lambda ,formals ,(simplify/maybe-wrap b bs))]
      [(list (? primitive? prim) args ...)
       (cons prim (map simplify args))]
      [(list proc args ...)
       (cons (simplify proc) (map simplify args))]
      [something-else
       (error 'remove-implicit-begin/when/unless
              (string-append
               "found ~s in processing input expr ~s"
               " (likely the prior pass's fault!)")
              x
              expr)]))

  ;; Lang1 Listof[Lang1] -> Lang2
  ;; since we don't know if the body need to be wrapped in a begin, this
  ;; helper simplifies the given bodies, decides if (begin ...) is necessary,
  ;; and wraps the bodies with it if so.
  (define (simplify/maybe-wrap b bs)
    (if (empty? bs)
        (simplify b)
        `(begin ,(simplify b) ,@(map simplify bs))))
  
  ;; simplify-decl : Id Lang1 -> Decl
  ;; helper for simplifying the RHS of a <Decl> from a let or letrec.
  (define (simplify-decl lhs rhs) (list lhs (simplify rhs)))
  
  ;; entry point:
  (simplify expr))

;; Aliases:
(define pass2 remove-implicit-begin/when/unless)
(define this-pass pass2)

(module+ test
  
  (compiler-tests/equal? remove-implicit-begin/when/unless
    (5                     5)
    ((if #t 5 6)           (if #t 5 6))
    ((if #t (if #f 7 8) 6) (if #t (if #f 7 8) 6))
    ((when #f 42)          (if #f 42 (void)))
    ((unless #f 42)        (if (not #f) 42 (void)))
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
     (let ([a 1][b 2]) (begin (set! b 4) (+ a b))))
    ((letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1))
     (letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1)))
    ((letrec ([f (lambda (n) (f n))])
       (set! f (lambda (n) (add1 n)))
       (add1 5))
     (letrec ([f (lambda (n) (f n))])
       (begin (set! f (lambda (n) (add1 n)))
              (add1 5))))
    ((let ([! (void)])
       (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
       (+ (! 5) 1))
     (let ([! (void)])
       (begin
         (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
         (+ (! 5) 1))))
    )
  
  ) ;; end test module