#lang racket
; STUDENT: Tejas Srikanth
; Student ID: tcsrikan
; Student Number: 20939242

; PARTNER: Anish Racharla
; Student ID: aracharl
; Student Number: 20951238

(define fun-ht (make-hash)) ; stores functions like so: { function-name: number of parameters }

; (compile-simpl s-code)
; takes in code in SIMPL-F and compiles
; it to A-PRIMPL
(define (compile-simpl s-code)
  (compile-simpl-firstpass s-code)
  (define is-main (hash-ref fun-ht 'main 'false))
  (cond
    [(equal? is-main 'false) (list 'data 0)]
    [else (append
           (list (list 'jump 'start-main))
           (compile-all-functions s-code)
           (list
            (list 'data 'RET-VAL 0)
            (list 'data 'RET-ADDR 'END)
            (list 'data 'FP 0)
            (list 'data 'SP 'END)
            (list 'label 'END)))]))

; (compile-all-functions lst)
; takes in SIMPL-F code in the form of a list
; outputs the code compiled to A-PRIMPL
(define (compile-all-functions lst)
  (cond
    [(empty? lst) empty]
    [else (append
           (compile-function (first lst))
           (compile-all-functions (rest lst)))]))

;;~~~FIRST PASS THROUGH PRIMPL CODE~~;;

; (process-fun-firstpass call)
; takes in a function header (ie (f x y))
; checks to see if there are duplicate functions of the
; same name, if there aren't it stores the function in fun-ht along with
; the number of parameters (ie (f x y) is stored as f: 2)
(define (process-fun-firstpass call)
  (define fun-name (first call))
  (define num-fun-params (length (rest call)))
  (define is-defined (hash-ref fun-ht fun-name 'false)) ; check fun-ht for function
  (cond
    [(equal? is-defined 'false) (hash-set! fun-ht fun-name num-fun-params)] ; name is unique
    [else (error "duplicate function name " fun-name)]))

; (compile-simpl-firstpass lst) takes in SIMPL-F code
; checks to see if there are any duplicate function names
; returns lst, and accumulates the functions in fun-ht, the associated
; value of each fun in fun-ht is its number of parameters
(define (compile-simpl-firstpass lst)
  (define fn (if (empty? lst) empty (first lst)))
  (match fn
      [(? empty? lst) empty]
      [`(fun ,call ,bdy) (process-fun-firstpass call)
                         (cons (first lst) (compile-simpl-firstpass (rest lst)))]))

;;~~~END FIRST PASS THROUGH PRIMPL CODE~~~;;;

;;~~~SECOND PASS THROUGH PRIMPL CODE~~~;;;

; (compile-function lst)
; takes in a function definition in SIMPL-F in
; list form and compiles it to A-PRIMPL
(define (compile-function lst)
  (define arg-lst (rest (second lst))) ; list or arguments
  (define loclst (second (third lst))) ; list of local variables
  (define varlst (append arg-lst loclst))
  (define len-frame (+ (length varlst) 2))
  (define bdy (rest (rest (third lst))))
  (define fn-name (first (second lst)))
  (append
   (gen-prologue fn-name varlst loclst len-frame)
   (compile-function-helper-err fn-name bdy)
   (gen-epilogue fn-name len-frame)))

; (gen-prologue fn varlst loclst len-frame)
; takes in the name of the function, fn
; takes in the list of variables (both locals and args),
; a list of local variables and their associated values,
; and the length of the stack frame of the function
(define (gen-prologue fn varlst loclst len-frame)
  (append
   (list (list 'label (string->symbol (~a 'start- fn))))
   (gen-consts fn varlst (check-vars-and-args fn varlst 2 (make-immutable-hash)))
   (move-vars fn loclst)
   (list
    (list 'move '(0 SP) 'FP)
    (list 'move '(1 SP) 'RET-ADDR)
    (list 'move 'FP 'SP)
    (list 'add 'SP 'SP len-frame))))

; (compile-function-helper-err fn bdy)
; takes in the function name and the body
; if the last statement in the body is not a return statement
; it errors out, otherwise compile the function
(define (compile-function-helper-err fn bdy)
  (define last-stmt (last bdy))
  (cond
    [(equal? (first last-stmt) 'return) (compile-function-helper fn bdy)]
    [else (error "return not last statement of function " fn)]))

; (compile-function-helper fn bdy)
; takes in a function name and body in list form
; compiles the function to A-PRIMPL from SIMPL-F
(define (compile-function-helper fn bdy)
  (cond
    [(empty? bdy) empty]
    [else (define firstItem (first bdy))
          (match firstItem
            [`(print ,aexpOrString) (append (translate-print fn aexpOrString)
                                            (compile-function-helper fn (rest bdy)))]
            [`(set ,id ,aexp) (append (translate-set fn id aexp)
                                      (compile-function-helper fn (rest bdy)))]
            [`(seq ,stmt ...) (append (translate-seq fn stmt)
                                      (compile-function-helper fn (rest bdy)))]
            [`(iif ,bexp ,stmt1 ,stmt2) (append (translate-iif fn bexp stmt1 stmt2)
                                                (compile-function-helper fn (rest bdy)))]
            [`(skip) (compile-function-helper fn (rest bdy))]
            [`(while ,bexp ,stmt ...) (append (translate-while fn bexp stmt)
                                              (compile-function-helper fn (rest bdy)))]
            [`(return ,aexp) (append (translate-return fn aexp)
                                     (compile-function-helper fn (rest bdy)))]
            )]))

; (gen-epilogue fn len-frame)
; takes in the function name and the length of a stack frame
; for the function
; generate the epilogue for the function
; generate the last 4 lines, which reset the stack frame
; and frame pointer
(define (gen-epilogue fn len-frame)
  (list
   (list 'label (string->symbol (~a 'end- fn)))
   (list 'sub 'SP 'SP len-frame)
   (list 'move 'FP '(0 SP))
   (list 'move 'RET-ADDR '(1 SP))
   (list 'jump 'RET-ADDR)))

; (check-vars-and-args fn varlst counter var-ht)
; takes in a function name, a list of variables (local and args), a counter variable
; and a hashtable for the variables
; checks for duplicates in function variables, if there are none returns the final value of
; var-ht
; in var-ht starting with args, each variable is given an index starting with 2
; so, if we have (list 'x 'y 'z), and 'x is an arg, we would have var-ht = { 'x: 2, 'y: 3, 'z: 4 }
(define (check-vars-and-args fn varlst counter var-ht)
  (cond
    [(empty? varlst) var-ht]
    [else (define curr-var (match (first varlst)
                             [(list var val) var]
                             [var var]))
          (define var-id (gen-id fn curr-var))
          (define is-defined (hash-ref var-ht var-id 'false))
          (cond
            [(equal? is-defined 'false) (define newht (hash-set var-ht var-id counter))
                                        (check-vars-and-args fn (rest varlst) (add1 counter) newht)]
            [else (error "duplicate variable name "curr-var)])]))

; (gen-consts fn varlst var-ht)
; this generates instructions for A-PRIMPL constants
; for each variable in varlst, associate this
; constant with a value starting with 2
; EX: if varlst was (list 'x 'y 'z), the call
; (gen-consts 'f varlst { 'x: 2, 'y: 3, 'z: 4 } )
; would generate
; '(
;   '(const _f_x 2)
;   '(const _f_y 3)
;   '(const _f_z 4))
(define (gen-consts fn varlst var-ht)
  (cond
    [(empty? varlst) empty]
    [else (define curr-var (match (first varlst)
                             [(list var val) var]
                             [var var]))
          (define var-id (gen-id fn curr-var))
          (cons
           (list 'const var-id (hash-ref var-ht var-id))
           (gen-consts fn (rest varlst) var-ht))]))

; Take in a function name and a list of local variables
; move the local variables into the stack frame for the function
; (the current stack frame)
(define (move-vars fn loclst) ; -- fn is a symbol, loclst contains elements of the form (var val) like (r 10)
  (cond
    [(empty? loclst) empty]
    [else (define loc-var (first loclst))
          (cons 
           (list 'move (list (gen-id fn (first loc-var)) 'SP) (second loc-var))
           (move-vars fn (rest loclst)))]))

; translate a print instruction in function
; (ie (print aexp))
; with name fn
(define (translate-print fn aexp)
  (match aexp
    [(? string? val) (list (list 'print-string aexp))]
    [else (define instr (process-aexp fn aexp))
          (append instr (list (list 'print-val '(0 SP))))]
    ))

; translate set instruction in function
; named fn, set id to value of aexp
; (ie (set id aexp))
(define (translate-set fn id aexp)
  (define instr (process-aexp fn aexp))
  (define newId (gen-id fn id))
  (append instr (list (list 'move (list newId 'FP) '(0 SP)))))

; translate a sequence of statements in function
; named fn
(define (translate-seq fn stmts)
  (compile-function-helper fn stmts))

; translate a return statement in function named fn
; ie (return aexp)
(define (translate-return fn aexp)
  (define instr (process-aexp fn aexp))
  (append instr (list
                (list 'move 'RET-VAL '(0 SP))
                (list 'jump (string->symbol (~a 'end- fn))))))

; translate iif statements in function with name fn
(define (translate-iif fn bexp stmt1 stmt2)
  (define l0 (gensym "LABEL0_"))
  (define l1 (gensym "LABEL1_"))
  (define l2 (gensym "LABEL2_"))
  (define bexpCode (process-bexp fn bexp))
  (define stmt1Code (compile-function-helper fn (list stmt1))) ;; compile-function-helper expects a list of statements, stmt1 & stmt2 are single statements
  (define stmt2Code (compile-function-helper fn (list stmt2)))
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
; translate while statements in function named fn
(define (translate-while fn bexp stmt)
  (define l0 (gensym "LABEL0_"))
  (define l1 (gensym "LABEL1_"))
  (define l2 (gensym "LABEL2_"))
  (define bexpCode (process-bexp fn bexp))
  (define stmtCode (compile-function-helper fn stmt)) ;; from compile-function-helper, stmt will already be a list of statment(s), no need use (list) here as in translate-iif
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
    [else #f]
    ))

; check if op is an actual binary op, otherwise
; return false
(define (isOp? op)
  (define is-op (opTrans op))
  (cond
    [(symbol? is-op) #t]
    [else #f]))

;; Processing a-expressions
;; process-aexp :: aexp -> (opd, (instructions))
;; We wish to place the result of each a-expression on the original top of the stack
;;  - the original top of the stack being the top of the stack process-aexp was called on the current aexp
(define (process-aexp fn aexpIn)
  (match aexpIn
    [(? number? val) (list (list 'move (list 0 'SP) val))]
    [(? symbol? val) (list (list 'move (list 0 'SP) (list (gen-id fn val) 'FP)))]
    [(list (? isOp? binOp) aexp1 aexp2) (define op1 (process-aexp fn aexp1))
                             (define op2 (process-aexp fn aexp2))
                             (append op1
                                     (list (list 'add 'SP 'SP 1))
                                     op2
                                     (list (list 'sub 'SP 'SP 1))
                                     (list (list (opTrans binOp) '(0 SP) '(0 SP) '(1 SP))))]
    [(list fn-called args ...) (process-function-call fn fn-called args)]
    ))

; for a function call, move the arguments into the next stack frame
; ie the call (f 2 1) moves arguments 2 and 1 into the next stack frame
; for f
(define (move-fn-args fn-caller fn-called args counter)
  (cond
    [(empty? args) empty]
    [else (append
           (process-aexp fn-caller (first args))
           (list (list 'add 'SP 'SP 1))
           (move-fn-args fn-caller fn-called (rest args) (add1 counter)))]))

; (process-function-call fn-caller fn-called args)
; takes in the caller function name, fn-caller, the called
; function's name fn-called, and a list of args being passed into
; fn-called
; compiles this function call from SIMPL-F to A-PRIMPL
(define (process-function-call fn-caller fn-called args)
  (define num-args (length args))
  (cond
  [(= num-args (hash-ref fun-ht fn-called))
  (append
   (list (list 'add 'SP 'SP 2))
   (move-fn-args fn-caller fn-called args 2)
   (list (list 'sub 'SP 'SP (+ num-args 2)))
   (list
    (list 'jsr 'RET-ADDR (string->symbol (~a 'start- fn-called)))
    (list 'move '(0 SP) 'RET-VAL)))]
  [else (error "supplied wrong number of arguments to "fn-called)]))

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
(define (process-bexp fn bexpIn)
  (match bexpIn
    [`true (list (list 'move (list 0 'SP) true))]
    [`false (list (list 'move (list 0 'SP) false))]
    [(list (? isEquality op) aexp1 aexp2) (define aexp1Code (process-aexp fn aexp1))
                                          (define aexp2Code (process-aexp fn aexp2))
                                          (append
                                           aexp1Code
                                           (list (list 'add 'SP 'SP 1))
                                           aexp2Code
                                           (list (list 'sub 'SP 'SP 1))
                                           (list (list (opTrans op) '(0 SP) '(0 SP) '(1 SP))))]
    [`(not ,bexp) (define bexpCode (process-bexp fn bexp))
                  (append
                   bexpCode
                   (list '(lnot (0 SP) (0 SP))))]
    [(list (or `and `or) bexp1 bexp2) (define op (opTrans (first bexpIn)))
                                      (define bexp1Code (process-bexp fn bexp1))
                                      (define bexp2Code (process-bexp fn bexp2))
                                      (append
                                       bexp1Code
                                       (list (list 'add 'SP 'SP 1))
                                       bexp2Code
                                       (list (list 'sub 'SP 'SP 1))
                                       (list (list op '(0 SP) '(0 SP) '(1 SP))))]
    ))
            

; generate ids for variables
; since all variables are bound by functions
; each variable will have name _fn_var
; so, if x is a local variable in f, (gen-id f x)
; turns into _f_x (useful for const declarations)

(define (gen-id fn var)
  (string->symbol (~a '_ fn '_ var)))



         
