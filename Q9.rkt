#lang racket
(define binOpHt
  (hash
   '+ 'add
   '* 'mul
   'div 'div
   'mod 'mod
   '= 'equal
   '> 'gt
   '< 'lt
   '<= 'le
   '>= 'ge
   'and 'land
   'or 'lor))

(define (binOpTrans binOp)
  (hash-ref binOpHt binOp))

(define (translate-binexp aexp)
  (cond
    [(symbol? aexp) (list
                      (list 'move '(0 SP) (string->symbol (~a '_ aexp)))
                      )]
    [(or (number? aexp) (boolean? aexp)) (list
                                           (list 'move '(0 SP) aexp)
                                           )]
    [(equal? (first aexp) 'not) (append
                                 (translate-binexp (second aexp))
                                 '(lnot (0 SP) (0 SP)))]
    [else (append
           (translate-binexp (second aexp))
           
           (cons
            '(add SP SP 1)
            (translate-binexp (third aexp)))
           (list
             (list 'sub 'SP 'SP 1)
             (list (binOpTrans (first aexp)) '(0 SP) '(0 SP) '(1 SP))))]))

(define (get-vars varlst acc)
  (cond
    [(empty? varlst) acc]
    [else (define firstvar (first varlst))
     (get-vars (rest varlst) (cons (list 'data
                 (string->symbol (~a '_ (first firstvar)))
                 (second firstvar)) acc))]))

(define (translate-print stmt)
  (cond
    [(string? (second stmt)) ('print-string stmt)]
    [else (define newlst (list 'print-val '(0 SP)))
     (append
           (translate-binexp (second stmt))
           (list newlst))]))

(define (translate-set stmt)
  (append
   (translate-binexp (second stmt))
   (list 'move (string->symbol (~a '_ (first stmt))) '(0 SP))
    ))

(define a '(vars
            [(x 2) (y 4)]
            (print (and (>= y (* 2 x)) (<= x y)))))

(define (compile-simpl-helper lst)
  (cond
    [(empty? lst) lst]
    [(equal? (first lst) 'vars) (append
                                (compile-simpl-helper (rest (rest lst)))
                                (get-vars (second lst) empty))]
    [(equal? (first (first lst)) 'print) (append
                                          (compile-simpl-helper (rest lst))
                                          (translate-print (first lst)))]
    [(equal? (first (first lst)) 'set) (translate-set (rest (first lst)))]))
             
  
(define (compile-simpl a-simpl)
  (define a-ap (compile-simpl-helper a-simpl))
  (define len-a (length a-ap))
  (append a-ap (list (list 'data 'SP (add1 len-a)))))
