#lang racket

(define ps-ht (make-hash))

(define (check-ht psymbol rec-depth num-psyms)
    (define val-ps (hash-ref ps-ht
                             psymbol
                             (lambda () (error "psymbol ~a undefined" psymbol))))
    (cond
      [(= rec-depth num-psyms) (error "circular")]
      [(number? val-ps) val-ps]
      [else
       (begin
         (define newval (check-ht val-ps (add1 rec-depth) num-psyms))
         (hash-set! ps-ht psymbol newval)
         newval)]))

(define (check-all-psyms num-psyms)
  (hash-for-each ps-ht
                 (lambda (psym val)
                         (check-ht psym 0 num-psyms))))

(define (print-ht)
  (hash-for-each ps-ht
                 (lambda (psym val)
                   (printf "~a ~a\n" psym val))))
      
(hash-set! ps-ht 'A 'B)
(hash-set! ps-ht 'B 'C)
(hash-set! ps-ht 'C 'D)
(hash-set! ps-ht 'D 'E)
(hash-set! ps-ht 'E 2)
(check-all-psyms 7)
(print-ht)