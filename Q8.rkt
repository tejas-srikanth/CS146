#lang racket
;GLOBAL HASHTABLES
(define ps-ht (make-hash)) ; hashtable for all psymbols
(define const-ht (make-hash)) ; hashtable for consts
(define label-ht (make-hash)) ; hashtable for labels
(define data-ht (make-hash)) ; hashtable for data

; (assembler-first-pass pcode)
; takes in A-PRIMPL code
; mutates the const-ht, data-ht, label-ht so that
; all consts, data, and labels
; are stored in their respective hashtables
; and all resolve to immediate values
; Ex:
; A call on (assembler-first-pass '(
;(const 'X 'Y)   [0]
;(data 'Y 1 1 2) [1, 2, 3]
;(label 'Z)      [4]
;(const 'E 'Z)   [5]
;(const 'A 'X)   [6]
;)

; Results in:
; ps-ht:
; { 'A: 1, 'X: 1, 'Y: 1, 'Z: 4, 'E: 4 }
; const-ht:
; { 'A: 1, 'X: 1, 'E: 4 }
; data-ht:
; { 'Y: 1 }
; const-ht
; { 'Z: 4 }
(define (assembler-first-pass pcode)
  (define num-consts (populate-hash pcode))
  (resolve-all-consts (+ 2 num-consts)))

; sample A-PRIMPL code
(define apcode
  '(
    (const X Y)
    (data Y 1 1 2)
    (label Z)
    (const E Z)
    (const A X)
    ))

(assembler-first-pass apcode)

(print-ht ps-ht)
(printf "\n")
(print-ht const-ht)
(printf "\n")
(print-ht data-ht)
(printf "\n")
(print-ht label-ht)

; (resolve-const-chain psymbol rec-depth num-psyms)
; psymbol is the first psymbol in the chain of declarations
; rec-depth is the recursive depth of the function
; num-psyms is the number of constants + 2

; mutates the ps-ht and the const-ht so that each
; const in a certain chain of const declarations
; is associated with an immediate value (ie a number
; or a boolean). Gives an error if variable is undefined
; or there is a circular reference
; Ex:
; ps-ht:
; { 'A: 2, 'E: 4, 'B: 'A, 'C: 'B, 'D: 'E }
; const-ht:
; { 'B: 'A, 'C: 'B, 'D: 'E }
; NOTE: in this case, the chain of const declarations is
; C -> B -> A
; (resolve-const-chain 'B 0 5)
; ps-ht:
; { 'A: 2, 'B: 2, 'C: 2, 'D: 'E }
; const-ht:
; { 'B: 2, 'C: 2, 'D: 'E }
; NOTE: 'D is not resolved as it's not in the const chain involving
; 'B
(define (resolve-const-chain psymbol rec-depth num-psyms)
    (define val-ps (hash-ref ps-ht
                             psymbol
                             (lambda () (error "undefined variable " psymbol))))
    (cond
      [(= rec-depth num-psyms) (error "circular reference involving " psymbol)] ; more calls than constants, must be a circular reference
      [(or (number? val-ps) (boolean? val-ps)) val-ps] ; value is immediate
      [else
       (begin
         (define newval (resolve-const-chain val-ps (add1 rec-depth) num-psyms)) ; resolve other consts in the chain
         (hash-set! ps-ht psymbol newval) ; mutate ps-ht and const-ht using the new value
         (hash-set! const-ht psymbol newval)
         newval)])); return the new value

; (resolve-all-consts num-psyms)
; num-psyms is the number of initialized consts + 2
; resolves all const chains, mutates ps-ht and const-ht
; so that each psymbol is resolved to an immediate value
; and not another psymbol
; Ex:
; ps-ht:
; { 'A: 2, 'E: 4, 'B: 'A, 'C: 'B, 'D: 'E }
; const-ht:
; { 'B: 'A, 'C: 'B, 'D: 'E }
; (resolve-const-chain 5)
; ps-ht:
; ; { 'A: 2, 'E: 4, 'B: 2, 'C: 2, 'D: 4 }
; const-ht:
; { 'B: 2, 'C: 2, 'D: 4 }
(define (resolve-all-consts num-psyms)
  (hash-for-each const-ht; iterate through the hashtable
                 (lambda (psym val)
                         (resolve-const-chain psym 0 num-psyms)))) ; resolve every const chain
; (populate-hah p-code)
; p-code is a list of a-primpl code
; pc is the current index of where we would be in the primpl
; vector
; num-consts is the number of defined constants, this
; will be what the function returns

; goes through A-primpl code and looks for consts
; data, and labels
; if it's (const var val):
;   if the psymbol hasn't been defined, add (key, val)=(var, val) to
;   ps-ht and const-ht and continue
; Similar if it's (label var) except add (key, pc) to label-ht and ps-ht
; where pc is the current index of the program
; Finally, if it's (data var val...), or (data var (repeat el)), store
; (var, pc) in data-ht and ps-ht
; Ex:
; A call on (populate-hash '(
;(const 'X 'Y)   [0]
;(data 'Y 1 1 2) [1, 2, 3]
;(label 'Z)      [4]
;(const 'E 'Z)   [5]
;(const 'A 'X)   [6]
;)
; Results in:
; ps-ht:
; { 'A: 'X, 'X: 'Y, 'Y: 1, 'Z: 2, 'E: 'Z }
; const-ht:
; { 'A: 'X, 'X: 'Y, 'E: 'Z }
; data-ht:
; { 'Y: 1 }
; const-ht
; { 'Z: 4 }
(define (populate-hash p-code)
  (define (ph-h primp-code pc num-consts)
    (cond
    [(empty? primp-code) num-consts]
    [else
    (define curr-inst (first primp-code))
    (match curr-inst
      [(list 'const var val) (begin
                               (define lookup (hash-ref ps-ht var "not-found"))
                               (cond
                                 [(equal? lookup "not-found") (hash-set! ps-ht var val) ; add it to ps-ht
                                                             (hash-set! const-ht var val) ;add it to const-ht
                                                             (ph-h (rest primp-code) (add1 pc) (add1 num-consts))]
                                 [else (error "duplicate key " var)]))] ; key found in ps-ht, error out
      [(list 'label var) (begin
                           (define lookup (hash-ref ps-ht var 'not-found))
                           (cond
                             [(equal? lookup "not-found") (hash-set! ps-ht var pc)
                                                        (hash-set! label-ht var pc) ; add to label-ht
                                                        (ph-h (rest primp-code) pc num-consts)] ; no need to increment pc
                             [else (error "duplicate key " var)]))]
      [(list 'data var (list repeat el)) (begin
                                           (define lookup (hash-ref ps-ht var 'not-found))
                                           (cond
                                             [(equal? lookup "not-found") (hash-set! ps-ht var pc)
                                                                         (hash-set! data-ht var pc) ; add to data-ht
                                                                         (ph-h (rest primp-code) (+ pc repeat) num-consts)] ; increment pc by repeat
                                                                                                                            ; as that's the index of next instruction in vector
                                             [else (error "duplicate key " var)]))]

      [(list 'data var val ...) (begin
                                 (define lookup (hash-ref ps-ht var 'not-found))
                                 (cond
                                   [(equal? lookup "not-found") (define data-len (length val))
                                                               (hash-set! ps-ht var pc)
                                                               (hash-set! data-ht var pc)
                                                               (ph-h (rest primp-code) (+ data-len pc) num-consts)] ; increment pc by the amount of data
                                   [else (error "duplicate key " var)]))]
      [_ (ph-h (rest primp-code) (add1 pc) num-consts)])])) ; otherwise continue
  (ph-h p-code 0 0))
                                   
; tester function, prints hashtable                                   
(define (print-ht ht)
  (hash-for-each ht
                 (lambda (psym val)
                   (printf "~a ~a\n" psym val))))
      

 
