#lang racket
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
the "else" case).
|#

; Output language, Lang2:
;
; <Exp>  ::= <Const>
;          | (quote <Lit>)
;          | <Var>
;          | (set! <Var> <Exp>)
;          | (if <Exp> <Exp> <Exp>)
;          | (begin <Exp> <Exp>*)
;          | (let (<Decl>*) <Exp>)
;          | (letrec (<Decl>*) <Exp>)
;          | (lambda (<Var>*) <Exp>)
;          | (<Prim> <Exp>*)
;          | (<Exp> <Exp>*)
; <Decl> ::= (<Var> <Exp>)

; Pass 3: remove-when&unless

; Input language is Lang2, and output is Lang3:
;
; <Exp>  ::= <Const>
;          | (quote <Lit>)
;          | <Var>
;          | (set! <Var> <Exp>)
;          | (when <Exp> <Exp>)          <-- Not in Lang3
;          | (unless <Exp> <Exp>)        <-- Not in Lang3
;          | (if <Exp> <Exp> <Exp>)
;          | (begin <Exp> <Exp>*)
;          | (let (<Decl>*) <Exp>)
;          | (letrec (<Decl>*) <Exp>)
;          | (lambda (<Var>*) <Exp>)
;          | (<Prim> <Exp>*)
;          | (<Exp> <Exp>*)
; <Decl> ::= (<Var> <Exp>)
