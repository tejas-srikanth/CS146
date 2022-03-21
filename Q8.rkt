#lang racket

(define ps-ht (make-hash))
(define const-ht (make-hash))
(define label-ht (make-hash))
(define data-ht (make-hash))


(define (resolve-const-chain psymbol rec-depth num-psyms)
    (define val-ps (hash-ref ps-ht
                             psymbol
                             (lambda () (error "undefined variable " psymbol))))
    (cond
      [(= rec-depth num-psyms) (error "circular reference involving " psymbol)]
      [(or (number? val-ps) (boolean? val-ps)) val-ps]
      [else
       (begin
         (define newval (resolve-const-chain val-ps (add1 rec-depth) num-psyms))
         (hash-set! ps-ht psymbol newval)
         (hash-set! const-ht psymbol newval)
         newval)]))

(define (resolve-all-consts num-psyms)
  (hash-for-each const-ht
                 (lambda (psym val)
                         (resolve-const-chain psym 0 num-psyms))))

(define (populate-hash p-code)
  (define (ph-h primp-code pc num-consts)
    (cond
    [(empty? primp-code) num-consts]
    [else
    (define curr-inst (first primp-code))
    (match curr-inst
      [(list 'const var val) (begin
                               (define lookup (hash-ref ps-ht var 'not-found))
                               (cond
                                 [(equal? lookup 'not-found) (hash-set! ps-ht var val)
                                                             (hash-set! const-ht var val)
                                                             (ph-h (rest primp-code) (add1 pc) (add1 num-consts))]
                                 [else (error "duplicate key " var)]))]
      [(list 'label var) (begin
                           (define lookup (hash-ref ps-ht var 'not-found))
                           (cond
                             [(equal? lookup 'not-found) (hash-set! ps-ht var pc)
                                                        (hash-set! label-ht var pc)
                                                        (ph-h (rest primp-code) pc num-consts)]
                             [else (error "duplicate key " var)]))]
      [(list 'data var (list repeat el)) (begin
                                           (define lookup (hash-ref ps-ht var 'not-found))
                                           (cond
                                             [(equal? lookup 'not-found) (hash-set! ps-ht var pc)
                                                                         (hash-set! data-ht var pc)
                                                                         (ph-h (rest primp-code) (+ pc repeat) num-consts)]
                                             [else (error "duplicate key " var)]))]

      [(list 'data var val ...) (begin
                                 (define lookup (hash-ref ps-ht var 'not-found))
                                 (cond
                                   [(equal? lookup 'not-found) (define data-len (length val))
                                                               (hash-set! ps-ht var pc)
                                                               (hash-set! data-ht var pc)
                                                               (ph-h (rest primp-code) (+ data-len pc) num-consts)]
                                   [else (error "duplicate key " var)]))]
      [_ (ph-h (rest primp-code) (add1 pc) num-consts)])]))
  (ph-h p-code 0 0))
                                   
                                   
(define (print-ht ht)
  (hash-for-each ht
                 (lambda (psym val)
                   (printf "~a ~a\n" psym val))))
      


(define pcode
  '(
    (const A B)
    (const B C)
    (const C A)
    (data D 4)
    ))

(define (assembler-first-pass pcode)
  (define num-consts (populate-hash pcode))
  (resolve-all-consts (+ 2 num-consts))) 
  
(assembler-first-pass pcode)

(print-ht ps-ht)
(printf "\n")
(print-ht const-ht)
(printf "\n")
(print-ht data-ht)
(printf "\n")
(print-ht label-ht)
