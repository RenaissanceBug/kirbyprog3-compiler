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
         | (begin <Exp> <Exp>*)     <--  modified by this pass.
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

(define (flatten-begin expr)
  (define (fb x)
    (match x
      [(? constant? c)   x]
      [(list 'quote lit) x]
      [(? symbol? id)    x]
      #;[(list 'set! (? symbol? lhs) rhs)
       ...]
      #;[(list 'if test e1 e2)
       ...]
      #;[(list 'begin e1)
       ...]
      #;[(list 'begin e1 e* ...)
       ...]
      #;[(list 'let (list (list (? symbol? lhs) rhs) ...) body)
       ...]
      #;[(list 'letrec (list (list (? symbol? lhs) rhs) ...) body)
       ...]
      #;[(list 'lambda (list (? symbol? formals) ...) body)
       ...]
      #;[(list (? primitive? prim) args ...)
       ...]
      #;[(list proc args ...)
       ...]
      #;[something-else
       (error 'flatten-begin
              (string-append
               "found ~s in processing input expr ~s"
               " (likely the prior pass's fault!)")
              x
              expr)]))
  ;; entry point:
  (fb expr))

(define pass3 flatten-begin)
(define this-pass pass3)

(module+ test
  
  (compiler-tests/equal? flatten-begin
    (5                     5)
    ((if #t 5 6)           (if #t 5 6))
    ; TO DO: add your tests here.
    ))