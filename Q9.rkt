#lang racket
;(require "PRIMPL-SIM.rkt" "Q8.rkt")
(define binOpHt
  (hash
   '+ 'add
   '* 'mul
   '- 'sub
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
    [(string? (second stmt)) (list (list 'print-string (second stmt)))]
    [else (define newlst (list 'print-val '(0 SP)))
     (append
           (translate-binexp (second stmt))
           (list newlst))]))

(define (translate-set stmt)
  (append
   (translate-binexp (second stmt))
   (list (list 'move (string->symbol (~a '_ (first stmt))) '(0 SP)))
    ))

(define (translate-iif stmt)
  (define test-exp (second stmt))
  (define tstmt (third stmt))
  (define fstmt (fourth stmt))
  (define label0-gen (gensym 'LABEL0))
  (define label1-gen (gensym 'LABEL1))
  (define label2-gen (gensym 'LABEL2))
  (append
   (translate-binexp test-exp)
   (list
    (list 'branch '(0 SP) label0-gen)
     (list 'jump label1-gen) 
    (list 'label label0-gen)
    )
   (compile-simpl-helper (list tstmt))
   (list
    (list 'jump label2-gen)
    (list 'label label1-gen))
   (compile-simpl-helper (list fstmt))
   (list
    (list 'label label2-gen))))

(define (translate-while do-stmt)
  (define test-exp (second do-stmt))
  (define stmt (rest (rest do-stmt)))
  (define label0-gen (gensym 'LABEL0))
  (define label1-gen (gensym 'LABEL1))
  (define label2-gen (gensym 'LABEL2))
  (append
   (list
    (list 'label label0-gen))
   (translate-binexp test-exp)
   (list
    (list 'branch '(0 SP) label1-gen)
    (list 'jump label2-gen)
    (list 'label label1-gen)
    )
   (compile-simpl-helper stmt)
   (list
    (list 'jump label0-gen)
    (list 'label label2-gen))))

(define (translate-skip stmt)
  empty)

(define (translate-seq stmt)
  (define actual-code (rest stmt))
  (append
   (compile-simpl-helper (list (first actual-code)))
  (compile-simpl-helper (rest actual-code))))

(define a '
(vars [(x 2) (y 0)]
      (seq
       (while (< y x)
              (print y)
              (print "\n"))
       (print "done"))

      )
  )

(define (compile-simpl-helper lst)
  (cond
    [(empty? lst) lst]
    [(equal? (first lst) 'vars) (append
                                (compile-simpl-helper (rest (rest lst)))
                                (get-vars (second lst) empty))]
    [(equal? (first (first lst)) 'seq) (append
                                        (translate-seq (first lst))
                                        (compile-simpl-helper (rest lst)))]
    [(equal? (first (first lst)) 'print) (append
                                          (translate-print (first lst))
                                          (compile-simpl-helper (rest lst))
                                          )]
    [(equal? (first (first lst)) 'set) (append
                                        (translate-set (rest (first lst)))
                                        (compile-simpl-helper (rest lst)))]
    [(equal? (first (first lst)) 'while) (append
                                          (translate-while (first lst))
                                          (compile-simpl-helper (rest lst)))]
    [(equal? (first (first lst)) 'iif) (append
                                         (translate-iif (first lst))
                                         (compile-simpl-helper (rest lst)))]
    [(equal? (first (first lst)) 'skip) (append
                                         empty
                                         (compile-simpl-helper (rest lst)))]))
             
  
(define (compile-simpl a-simpl)
  (define a-ap (compile-simpl-helper a-simpl))
  (define len-a (length a-ap))
  (append a-ap (list (list 'data 'SP (add1 len-a)))))

(define aprimp-code (compile-simpl a))
aprimp-code

;((while (<= inner outer) (iif (= (mod inner 2) (* x 0)) (seq (print outer) (print  ) (print inner) (print 
;)) (print inner is odd
;)) (set inner (+ inner 1))) (set outer (+ outer 1)))
