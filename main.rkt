#lang racket

(require "support/compiler-testing.rkt"
         "pass1.rkt"
         "pass2.rkt"
         "pass3-flatten-begin.rkt"
         "pass4-quote-constants.rkt"
         "pass5-uncover.rkt"
         "pass6-elr.rkt"
         "pass7-remove-impure-letrec.rkt"
         "pass8-box-settables.rkt"
         "pass9-sanitize-binding.rkt"
         )

(provide compile)

(define compile
  (apply compose
         (reverse (list pass1 pass2 pass3 pass4 pass5 pass6 pass7 pass8
                        pass9))))

(module+ test
  (require rackunit)
  (define-namespace-anchor a)
  (define ns (namespace-anchor->namespace a))
  (namespace-set-variable-value! 'error
                                 (lambda (ls) (error (list->string ls)))
                                 #t
                                 ns)
  (define (eval-compiled expr) (eval expr ns))
  (compiler-tests/eval=? compile
    eval-compiled
    5
    #t
    #f
    #\a
    (if #t 5 6)
    (if #f 5 6)
    (if #t (if #f 7 8) 6)
    (when #f 42)
    (unless #f 42)
    (let ([x 0]) (set! x (add1 x)) x)
    (let ([a 1][b 2]) (begin a b))
    (let ([a 1]) a)
    (let ([a 1][b 2]) (set! b 4) (+ a b))
    (letrec ([! (lambda (n) (if (= n 0) 1 (* n (! (- n 1)))))]) (+ (! 5) 1))
    (let ([! (void)])
      (set! ! (lambda (n) (if (= n 0) 1 (* n (! (- n 1))))))
      (+ (! 5) 1))
    (letrec ([x (letrec ([g (lambda () '0)]
                         [h (lambda () y)])
                  (lambda ()
                    (cons g (cons h '()))))]
             [y '2])
      (let ([f1 (car (x))][f2 (car (cdr (x)))])
        (cons (f1) (cons (f2) (cons y '())))))
    )
  
  (define (letrec-violation? x)
    (and (exn:fail? x) (equal? (exn-message x) "detected letrec violation")))
  
  (define-syntax-rule (check-letrec-violation? expr)
    (check-exn letrec-violation?
      (lambda ()
        (eval-compiled
         (compile 'expr)))))
  
  (check-letrec-violation?
   (let ([f '#f])
     (letrec ([x (begin (set! f (lambda () (+ '1 y)))
                        (f))]
              [y '0])
       (cons x (cons y '())))))
  
  (check-letrec-violation?
   (let ([v (make-vector '1)])
     (letrec ([x (begin (vector-set! v '0 (lambda () (+ '1 y)))
                        ((vector-ref v '0)))]
              [y '1])
       (cons x (cons y '())))))
  
  (check-letrec-violation?
   (letrec ([x (letrec ([g (lambda () (h))]
                        [h (lambda () y)])
                 (g))]
            [y '2])
     (cons x (cons y '()))))

  (define-syntax-rule (check-arity-violation? expr)
    (check-exn #rx"arity mismatch" (lambda () (compile 'expr))))

  (check-arity-violation? ((lambda () 1) 2))
  (check-arity-violation? ((lambda (x y z) (* x y z)) 1 2))
  (check-arity-violation? (letrec ()
                            ((lambda (pi r) (* 2 pi r)) 2 3.14 10)))
  )

