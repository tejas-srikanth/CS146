#lang racket
; CS146 - Q8: A-PRIMPL to PRIMPL
; Winter 22
;
; writing an assembler

;; Currently nets 15/17
;; known issues:
;;  - circular const definitions

;;~~~~~~PROGRAM~~~~~~;;
;; Structs for the various psymbol types
(struct data (index) #:transparent)
(struct const (value) #:transparent)
(struct label (index) #:transparent)

(define (primpl-assemble aPrimpInstr)
  (define (assemble-h primpInstr)
    (hash-clear! psHash)
    primpInstr)
  (first-pass aPrimpInstr)
  (assemble-h (second-pass aPrimpInstr)))

(define psHash (make-hash)) ;; The psymbol hash-table

(define (first-pass aPrimpInstr)
  (populate-table aPrimpInstr)
  (resolve-table))

(define (populate-table aPrimpInstr)
  (define (populate-table-h aPrimp index)
    (cond
      [(empty? aPrimp) (void)]
      [else
       (match (first aPrimp)
         [`(const ,psymb ,psymbOrVal) (begin (define lookupPsymb (hash-ref psHash psymb 'notFound))
                                             (define newVal (const psymbOrVal))
                                             (cond
                                               [(eq? 'notFound lookupPsymb)
                                                (hash-set! psHash psymb newVal)
                                                (populate-table-h (rest aPrimp) index)] ; no need to increment index
                                               [else (error "duplicate key: " psymb)]))]
         [`(label ,psymb) (begin (define lookupPsymb (hash-ref psHash psymb 'notFound))
                                 (define newVal (label index))
                                 (cond
                                   [(eq? 'notFound lookupPsymb)
                                    (hash-set! psHash psymb newVal)
                                    (populate-table-h (rest aPrimp) index)] ; no need to increment index
                                   [else (error "duplicate key: " psymb)]))]
         [`(data ,psymb (,nat ,psymbOrVal)) (begin (define lookupPsymb (hash-ref psHash psymb 'notFound))
                                                   (define newVal (data index))
                                                   (cond
                                                     [(eq? 'notFound lookupPsymb)
                                                      (hash-set! psHash psymb newVal)
                                                      (populate-table-h (rest aPrimp) (+ index nat))]; since the are nat # of values, increase index by nat
                                                     [else (error "duplicate key: " psymb)]))]
         [`(data ,psymb ,psymbOrVal ...) (begin (define lookupPsymb (hash-ref psHash psymb 'notFound))
                                                (define newVal (data index))
                                                (cond
                                                  [(eq? 'notFound lookupPsymb)
                                                   (hash-set! psHash psymb newVal)
                                                   (populate-table-h (rest aPrimp) (+ index (length psymbOrVal)))]
                                                  [else (error "duplicate key: " psymb)]))]
         [_ (populate-table-h (rest aPrimp) (add1 index))]
         )]))
  (populate-table-h aPrimpInstr 0))

(define (resolve-table)
  (define (get-val val)
    (cond
      [(const? val) (const-value val)]
      [(data? val) (data-index val)]
      [(label? val) (label-index val)]))
  (define (resolve-table-init key val)
    (cond
      [(const? val) (cond
                      [(symbol? (const-value val))
                       (define psymb (const-value val))
                       (hash-set! psHash key (const (resolve-table-init psymb (hash-ref psHash psymb (λ () (error "undefined psymb: " psymb))))))
                       (get-val (hash-ref psHash psymb))]
                      [else (const-value val)])]
      [(data? val) (data-index val)]
      [(label? val) (label-index val)]
      [else (error "unexpeted psymbol type in table: " val)]))
  (hash-for-each psHash resolve-table-init)
  )

(define (second-pass aPrimpInstr)
  (define (second-pass-helper aPrimp primpInstr)
    (cond
      [(empty? aPrimp) primpInstr]
      [else 
       (define curr (first aPrimp))
       (match curr
         [`(halt) (second-pass-helper (rest aPrimp) (cons 0 primpInstr))]
         [`(lit ,psymbOrVal) (second-pass-helper (rest aPrimp) (cons (produce-lit psymbOrVal) primpInstr))]
         [`(const ,name ,val) (second-pass-helper (rest aPrimp) primpInstr)] ; no need to add anything to the output
         [`(data ,name (,nat ,val)) (second-pass-helper (rest aPrimp)
                                                        (append (build-list nat (λ (x) (produce-lit val))) primpInstr))]
         [`(data ,name ,val ...) (second-pass-helper (rest aPrimp)
                                                     (append (foldl (λ (x y) (cons (produce-lit x) y)) empty val) primpInstr))]
         [`(label ,name) (second-pass-helper (rest aPrimp) primpInstr)]
         [`(jump ,loc) (second-pass-helper (rest aPrimp)
                                           (cons (list 'jump (produce-jb-loc loc)) primpInstr))]
         [`(branch ,opd ,loc) (second-pass-helper (rest aPrimp)
                                                  (cons (list 'branch (produce-opd opd) (produce-jb-loc loc))
                                                        primpInstr))]
         [`(print-val ,opd) (second-pass-helper (rest aPrimp)
                                                (cons (list 'print-val (produce-opd opd)) primpInstr))]
         [`(print-string ,str) (second-pass-helper (rest aPrimp)
                                                   (cons (list 'print-string str) primpInstr))]
         [`(,op ,dest ,opd1 ,opd2) (second-pass-helper (rest aPrimp) ;; Binary operations
                                                       (cons (list op (produce-dest dest) (produce-opd opd1) (produce-opd opd2)) primpInstr))]
         [`(,op ,dest ,opd) (second-pass-helper (rest aPrimp) ;; Unary operations
                                                (cons (list op (produce-dest dest) (produce-opd opd)) primpInstr))])]))
  (define (produce-indexed-access imm ind)
    (define (process-imm im)
      (match im
        [(? symbol? im) (define lookup (hash-ref psHash im (λ () (error "undefined psymb: " im))))
                        (cond
                          [(data? lookup) (data-index lookup)]
                          [(const? lookup) (const-value lookup)]
                          [(label? lookup) (error "incorrect use of label: " im lookup)]
                          [else (error "process-imm symbol")])]
        [im im])) ;; assuming there is a non-psymb imm here
    (define (process-ind in)
      (match in
        [(? symbol? in) (define lookup (hash-ref psHash in (λ () (error "undefined psymb: " in))))
                        (cond
                          [(data? lookup) (list (data-index lookup))]
                          [(const? lookup) (error "incorrect use of const: " in lookup)]
                          [(label? lookup) (error "incorrect use of label: " in lookup)]
                          [else (error "produce-ind symbol")])]
        [in in])) ;; assuming there is a non-psymb ind value here
    (list (process-imm imm) (process-ind ind)))
  (define (produce-dest val)
    (match val
      [`(,imm ,ind) (produce-indexed-access imm ind)]
      [(? symbol? v) (define lookup (hash-ref psHash v (λ () (error "undefined psymb: " v))))
                     (cond
                       [(data? lookup) (list (data-index lookup))]
                       [(const? lookup) (error "incorrect use of const: " v lookup)]
                       [(label? lookup) (error "incorrect use of label: " v lookup)]
                       [else (error "produce-opd symbol")])]
      [val val]))
  (define (produce-opd val)
    (match val
      [`(,imm ,ind) (produce-indexed-access imm ind)]
      [(? symbol? v) (define lookup (hash-ref psHash v (λ () (error "undefined psymb: " v))))
                     (cond
                       [(data? lookup) (list (data-index lookup))]
                       [(const? lookup) (const-value lookup)]
                       [(label? lookup) (error "incorrect use of label: " v lookup)]
                       [else (error "produce-opd symbol")])]
      [val val]))
  (define (produce-lit psymbOrVal) ; processes pseudo-instr arguments
    (cond
      [(symbol? psymbOrVal) ; if a symbol, check the psHash
       (define lookup (hash-ref psHash psymbOrVal (λ () (error "undefined psymb: " psymbOrVal))))
       (cond
         [(data? lookup) (data-index lookup)]
         [(const? lookup) (const-value lookup)]
         [(label? lookup) (label-index lookup)]
         [else (error "produce-lit symbol")])]
      [else psymbOrVal])) ; if not a symbol, assume it's a valid type
  (define (produce-jb-loc val) ; processes jump/branch targets
    (cond
      [(symbol? val) ;; special conditions for jump/branch target psymbols
       (define lookup (hash-ref psHash val (λ () (error "undefined psymb: " val))))
       (cond 
         [(label? lookup) (label-index lookup)]
         [(data? lookup) (list (data-index lookup))] ;; data and const treated as indirects
         [(const? lookup) (list (const-value lookup))]
         [else (error "produce-jb-loc symbol")])]
      [else (produce-opd val)] ;; otherwise, produce opd as usual (psymb cases already covered)
      ))
  (reverse (second-pass-helper aPrimpInstr empty))
  )
;;~~~~~~END-PROGRAM~~~~~~;;

;;~~~~~~~~~~~TESTING~~~~~~~~~~~;;
;; Test cases
(define test-code
  '(
    (const A X)
    (label B)
    (lit 1)
    (data D 1 2 3 4)
    (data C (3 1))
    ))

(define test-code-2
  '(
    (lit 0)
    (data A 2)
    (data B (5 A))
    (data D 3 4)
    (halt)
    ))

(define test-code-3
  '(
    (const A 2)
    (data B 0)
    (add B (5) A)
    (mul (1) 2 (1))
    (halt)
    ))

(define test-code-4
  '(
    (data X 1)
    (add X (X X) (2 X))
    ))

(define test-code-5
  '(
    (data B #true)
    (label A)
    (add (0) 1 1)
    (jump A)
    (branch B A)
    (print-val B)
    ))

;; Print ht
(define (print-ht ht)
  (hash-for-each ht (λ (psymb val) (printf "~a ~a\n" psymb val))))
  
;; Individual testing
;(print-ht psHash)
;(populate-table test-code-2)
;(print-ht psHash)
;(newline)

;(resolve-table)
;(print-ht psHash)

;(second-pass test-code-2)




; Final function testing
;(primpl-assemble test-code-5)


;;~~~~~~~~~~~END-TESTING~~~~~~~~~~~;;


;;~~~~~~~~~~~NOTES~~~~~~~~~~~;;
; labels are only allowed to be used in:
;  - jump
;  - branch
;  - const
;  - data
;  - lit
; Note, it is always used as an immediate

; Jump and Branch locations:
; - labels treated as imm
; - const and data treated as ind
; - other opnds as normal

; Data:
; Treated as imm:
; - in data instructions
; - in const instructions
; - in lit
; - in first position of indexed access
; Treated as ind:
; - everywhere else

; Const:
; Treated as ind:
; - jump and branch targets
; Treated as imm:
; everywhere else
