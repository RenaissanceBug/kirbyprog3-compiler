#lang racket

(require "support/helpers.rkt")

(provide pass3 flatten-begin)

(module+ test
  (require rackunit
           "support/compiler-testing.rkt"))

#|
Pass 3: flatten-begin : Lang2 -> Lang3

This pass removes nested begin-expressions, and removes unary
begin-expressions; in its output, a begin-expression contains two or more
subexpressions, neither of which may also be a begin expression.  For
example,

       (begin (begin 4 5 6) 7 (begin 8 (begin 9 0)))
              ==> (begin 4 5 6 7 8 9 0)
and
      (begin 6)
              ==> 6

Input language, Lang2:

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

The output language grammar, Lang3, is:

    <Exp> ::= (begin <NB-Exp> <NB-Exp>+)
           | <NB-Exp>

 <NB-Exp> ::= <Const>
           | (quote <Lit>)
           | <Var>
           | (set! <Var> <Exp>)
           | (if <Exp> <Exp> <Exp>)
           | (let (<Decl>*) <Exp>)
           | (letrec (<Decl>*) <Exp>)
           | (lambda (<Var>*) <Exp>)
           | (<Prim> <Exp>*)
           | (<Exp> <Exp>*)

  <Decl> ::= (<Var> <Exp>)

|#

;; flatten-begin : Lang2 -> Lang3:Exp
(define (flatten-begin expr)
  ;; fb : Lang2 -> Lang3:Exp
  ;; main recursive function
  (define (fb x)
    (match x
      [(? constant? c)   x]
      [(list 'quote lit) x]
      [(? symbol? id)    x]
      [(list 'set! (? symbol? lhs) rhs)
       `(set! ,lhs ,(fb rhs))]
      [(list 'if test e1 e2)
       `(if ,(fb test) ,(fb e1) ,(fb e2))]
      [(list 'begin e1)
       (fb e1)]
      [(list 'begin e1 e* ...)
       `(begin ,@(lang3-exps->nb-exps (map fb (cons e1 e*))))]
      [(list 'let (list (list (? symbol? lhs) rhs) ...) body)
       `(let ,(map (λ (L R) (list L (fb R))) lhs rhs)
          ,(fb body))]
      [(list 'letrec (list (list (? symbol? lhs) rhs) ...) body)
       `(letrec ,(map (λ (L R) (list L (fb R))) lhs rhs)
          ,(fb body))]
      [(list 'lambda (list (? symbol? formals) ...) body)
       `(lambda ,formals ,(fb body))]
      [(list (? primitive? prim) args ...)
       `(,prim ,@(map fb args))]
      [(list proc args ...)
       (map fb (cons proc args))]
      [something-else
       (error 'flatten-begin
              "something is badly wrong; found ~s in processing input expr: ~s"
              x
              expr)]))
  
  ;; lang3-exps->nb-exps : Listof[Lang3:Exp] -> Listof[Lang3:NB-Exp]
  (define (lang3-exps->nb-exps exps)
    (cond [(empty? exps) empty]
          [(cons? exps)
           (let ([NB-exps (lang3-exps->nb-exps (rest exps))])
             (match (first exps)
               [(list 'begin es ...)
                (append es NB-exps)]
               [NB-exp
                (cons NB-exp NB-exps)]))]))
  
  ;; entry point:
  (fb expr))

(define pass3 flatten-begin)
(define this-pass pass3)

(module+ test
  
  (compiler-tests/equal? flatten-begin
    (5                     5)
    ((if #t 5 6)           (if #t 5 6))
    ((if #t (if #f 7 8) 6) (if #t (if #f 7 8) 6))
    ((let ([x 0])
       (begin (set! x (add1 x))
              x))
     (let ([x 0])
       (begin (set! x (add1 x))
              x)))
    ((begin 1 2) (begin 1 2))
    ((begin (begin 1 2 (begin 3) (begin 4 (begin 5 6 7))) 8 9)
     (begin 1 2 3 4 5 6 7 8 9))
    ((let ([a 1][b 2]) (begin a (begin b a)))
     (let ([a 1][b 2]) (begin a b a)))
    ((let ([a 1]) a)
     (let ([a 1]) a))
    ((let ([a 1][b 2]) (begin (set! b 4) (+ a b)))
     (let ([a 1][b 2]) (begin (set! b 4) (+ a b))))
    ((letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1))
     (letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))])
       (+ (! 5) 1)))
    ((letrec ([f (lambda (n) (f n))])
       (begin (set! f (lambda (n) (add1 n)))
              (begin (set! f (lambda (n) (+ 2 n)))
                     (f 5))))
     (letrec ([f (lambda (n) (f n))])
       (begin (set! f (lambda (n) (add1 n)))
              (set! f (lambda (n) (+ 2 n)))
              (f 5))))
    ((let ([! (void)]
           [x 5])
       (begin (begin (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
                     (set! x (add1 x)))
              (! x)))
     (let ([! (void)]
           [x 5])
       (begin (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
              (set! x (add1 x))
              (! x))))
    ))
