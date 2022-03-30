; Partner: Tejas Srikanth
; Student ID: tcsrikan
; Student Number: 20939242

#|
                   CS146 : Q9
    Program title:         SIMPL compiler
    Programmed by:         Anish Racharla
    Date:                  Mon, 22/3/28


    Description: Compiling from SIMPL to A-PRIMPL
|#

;;~~~~~~Problem information~~~~~~;;
;; We are writing a program to compile SIMPL and turn it into a set of A-PRIMPL instructions
;;  which could be taken by our A-PRIMPL assembler to be turned into runnable PRIMPL code.

;;~~~~End Problem information~~~~;;

;;~~~~~~~~General Defns~~~~~~~~;;
#lang racket

;;~~~~~~End General Defns~~~~~~;;

;;~~~~~~~~Solution~~~~~~~~;;
;; The Main Function:
(define (compile-simpl simpl)
  (define aprimp (compile-helper simpl))
  (define aprimpLen (length aprimp))
  (append aprimp (list (list 'data 'SP (add1 aprimpLen)))))

;; Statment compiler
;; takes in a list of statments and outputs a list of corresponding A-PRIMPL instructions
(define (compile-helper simpl)
  (cond
    [(empty? simpl) empty]
    [else (define firstItem (first simpl))
          (match firstItem
            [`vars (append (compile-helper (rest (rest simpl)))
                           '((halt))
                           (vars-helper (second simpl)))]
            [`(print ,aexpOrString) (append (translate-print aexpOrString)
                                            (compile-helper (rest simpl)))]
            [`(set ,id ,aexp) (append (translate-set id aexp)
                                      (compile-helper (rest simpl)))]
            [`(seq ,stmt ...) (append (translate-seq stmt)
                                      (compile-helper (rest simpl)))]
            [`(iif ,bexp ,stmt1 ,stmt2) (append (translate-iif bexp stmt1 stmt2)
                                                (compile-helper (rest simpl)))]
            [`(skip) (compile-helper (rest simpl))]
            [`(while ,bexp ,stmt ...) (append (translate-while bexp stmt)
                                              (compile-helper (rest simpl)))]
            )]
    )
  )

(define (vars-helper varsList)
  (define (vars-h varsIn dataOut)
    (cond
      [(empty? varsIn) dataOut]
      [else (define id (first (first varsIn)))
            (define num (second (first varsIn)))
            (define newID (gen-id id))
            (vars-h (rest varsIn) (cons (list 'data newID num) dataOut))]
      )
    )
  (vars-h varsList empty)
  )

;; Statement translation helpers
;; - take in the statement and output a list of corressponding A-primpl instructions

(define (translate-print aexp)
  (match aexp
    [(? string? val) (list (list 'print-string aexp))]
    [else (define instr (process-aexp aexp))
          (append instr (list (list 'print-val '(0 SP))))]
    ))

(define (translate-set id aexp)
  (define instr (process-aexp aexp))
  (define newId (gen-id id))
  (append instr (list (list 'move newId '(0 SP)))))

(define (translate-seq stmts)
  (compile-helper stmts))

(define (translate-iif bexp stmt1 stmt2)
  (define l0 (gensym "LABEL0_"))
  (define l1 (gensym "LABEL1_"))
  (define l2 (gensym "LABEL2_"))
  (define bexpCode (process-bexp bexp))
  (define stmt1Code (compile-helper (list stmt1))) ;; compile-helper expects a list of statements, stmt1 & stmt2 are single statements
  (define stmt2Code (compile-helper (list stmt2)))
  (append bexpCode
          (list (list 'branch '(0 SP) l0))
          (list (list 'jump l1))
          (list (list 'label l0))
          stmt1Code
          (list (list 'jump l2))
          (list (list 'label l1))
          stmt2Code
          (list (list 'label l2))
          ))

(define (translate-while bexp stmt)
  (define l0 (gensym "LABEL0_"))
  (define l1 (gensym "LABEL1_"))
  (define l2 (gensym "LABEL2_"))
  (define bexpCode (process-bexp bexp))
  (define stmtCode (compile-helper stmt)) ;; from compile-helper, stmt will already be a list of statment(s), no need use (list) here as in translate-iif
  (append (list (list 'label l0))
          bexpCode
          (list (list 'branch '(0 SP) l1))
          (list (list 'jump l2))
          (list (list 'label l1))
          stmtCode
          (list (list 'jump l0))
          (list (list 'label l2))
          ))


;; Operator translator
(define (opTrans op)
  (match op
    [`+ 'add]
    [`- 'sub]
    [`* 'mul]
    [`div 'div]
    [`mod 'mod]
    ['= 'equal]
    ['> 'gt]
    ['< 'lt]
    ['>= 'ge]
    ['<= 'le]
    ['and 'land]
    ['or 'lor]
    ))

;; Processing a-expressions
;; process-aexp :: aexp -> (opd, (instructions))
;; We wish to place the result of each a-expression on the original top of the stack
;;  - the original top of the stack being the top of the stack process-aexp was called on the current aexp
(define (process-aexp aexpIn)
  (match aexpIn
    [(? number? val) (list (list 'move (list 0 'SP) val))]
    [(? symbol? val) (list (list 'move (list 0 'SP) (gen-id val)))]
    [`(,binOp ,aexp1 ,aexp2) (define op1 (process-aexp aexp1))
                             (define op2 (process-aexp aexp2))
                             (append op1
                                     (list (list 'add 'SP 'SP 1))
                                     op2
                                     (list (list 'sub 'SP 'SP 1))
                                     (list (list (opTrans binOp) '(0 SP) '(0 SP) '(1 SP))))]
    ))

(define EqualityTable
  (hash
   '= true
   '> true
   '< true
   '>= true
   '<= true))

(define (isEquality op)
  (hash-ref EqualityTable op false))

;; Processing b-expressions
;; very similar to processing aexps
(define (process-bexp bexpIn)
  (match bexpIn
    [`true (list (list 'move (list 0 'SP) true))]
    [`false (list (list 'move (list 0 'SP) false))]
    [(list (? isEquality op) aexp1 aexp2) (define aexp1Code (process-aexp aexp1))
                                          (define aexp2Code (process-aexp aexp2))
                                          (append
                                           aexp1Code
                                           (list (list 'add 'SP 'SP 1))
                                           aexp2Code
                                           (list (list 'sub 'SP 'SP 1))
                                           (list (list (opTrans op) '(0 SP) '(0 SP) '(1 SP))))]
    [`(not ,bexp) (define bexpCode (process-bexp bexp))
                  (append
                   bexpCode
                   (list '(lnot (0 SP) (0 SP))))]
    [(list (or `and `or) bexp1 bexp2) (define op (opTrans (first bexpIn)))
                                      (define bexp1Code (process-bexp bexp1))
                                      (define bexp2Code (process-bexp bexp2))
                                      (append
                                       bexp1Code
                                       (list (list 'add 'SP 'SP 1))
                                       bexp2Code
                                       (list (list 'sub 'SP 'SP 1))
                                       (list (list op '(0 SP) '(0 SP) '(1 SP))))]
    ))

;; appending '_' to the beggining of SIMPL vars
(define (gen-id id)
  (string->symbol (string-append "_" (symbol->string id))))

;;~~~~~~End Solution~~~~~~;;

;;~~~~~~Testing~~~~~~;;
(define test1
  '(vars [(a 1) (b 2)]
         (print a)
         (print "test")
         ))

(define test2
  '(vars [(a 1)]
         ;(print (+ a a))
         (set a (+ (+ 1 2) 3))
         ))

(define test3
  '(vars []
         (seq
          (print "test"))))

;; bexps
(define test4
  '(vars []
         (iif (<= 1 1)
              (print "true")
              (print "false")
              )
         )
  )

;; while
(define test5
  '(vars []
         (while (and true true)
                (print "test1")
                (print "test2")
                )))

;(compile-simpl test5)

;;~~~End Of Testing~~~;;


