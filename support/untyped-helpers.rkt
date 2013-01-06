#lang racket

(provide build-begin)

;; NEListof[Expr] -> Expr
;; Converts the list of exprs to a begin-expression with no immediately-nested
;; begin-exprs.
(define (build-begin exprs)
  (cons 'begin (foldr cons-or-append empty exprs)))

;; Expr Listof[Expr] -> NEListof[Expr]
(define (cons-or-append e ls)
  (match e
    [(list 'begin e* ...)
     (append e* ls)]
    [e
     (cons e ls)]))