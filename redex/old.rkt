#lang racket
(require redex)

(define-language IPPC
  (THREAD ::= (thread STACK CHUNK-STORE PROGRAM FUEL BB))
  (FUEL ::= number)
  (STACK ::= (stack FRAME ...))
  (FRAME ::= (frame ACTIVATION-ID CFG-LABEL TRAMPOLINE ARG ...)) ; stack frame
  (ACTIVATION-ID ::= variable-not-otherwise-mentioned) ; unique id of a stack frame
  (TRAMPOLINE ::= (BB-LABEL BB-LABEL)) ; the trampoline consists of a pair
                                       ; of basic-block labels, namely
                                       ;  (predecessor, successor)
                                       ; where predecessor refers to the current
                                       ; basic block and successor to the next one.
  (ARG ::= (VAR MACHINE-VAL)) ; function argument
  
  (MACHINE-VAL ::=
               (mv-number number)
               (mv-csl CHUNK-STORE-LOCATION)
               (mv-ipfs-hash IPFS-HASH)
               (mv-var VAR))  ; implicitly performs a frame-load
  (IPFS-HASH ::= number)

  (CHUNK-STORE ::= ((CHUNK-STORE-LOCATION CHUNK) ...))
  (CHUNK-STORE-LOCATION ::= number)
  (CHUNK ::= ; every chunk is represented by a chunk object
             ; and its associated header object.
             ; the header object stores a pointer to its
             ; chunk object and optionally the ipfs hash
             ; code of the chunk object.
         (chunk-header CHUNK-STORE-LOCATION IPFS-HASH ...)
         (chunk MACHINE-VAL ...))
  
  (PROGRAM ::= (program CFG ...))
  (CFG ::= (cfg CFG-LABEL (BB ...))) ; function (represented by control-flow graph)
  (BB ::= (basic-block BB-LABEL INSTRS CONTROL-OP)) ; basic block
  (CONTROL-OP ::=
              (jump BB-LABEL)
              (conditional-jump MACHINE-VAL BB-LABEL ...) ; (conditional-jump i lab ...)
                                                          ; jump to ith basic-block label in lab ...
              (call CFG-LABEL BB-LABEL (VAR MACHINE-VAL) ...)   ; (call f lab args ...)
                                                                ; call function f passing argument list
                                                                ; args ..., and upon return jumping to
                                                                ; basic block with label lab
              (return))
  (INSTRS ::= (INSTR ...))
  (INSTR ::=
         (frame-store VAR MACHINE-VAL)
         (chunk-alloc VAR MACHINE-VAL)
         (chunk-load VAR MACHINE-VAL)
         (chunk-store VAR MACHINE-VAL MACHINE-VAL)
         (arith VAR OP MACHINE-VAL ...))
  (OP ::= + - * /)
       
  (BB-LABEL ::= variable-not-otherwise-mentioned (return-label) (entry-label)) ; basic-block label
  (CFG-LABEL ::= variable-not-otherwise-mentioned) ; CFG/function label
  (VAR ::= variable-not-otherwise-mentioned)) ; frame-bound variable

(define-metafunction IPPC
  lookup-function : PROGRAM CFG-LABEL -> CFG
  [(lookup-function (program
                     (cfg CFG-LABEL_before (BB_before ...)) ...
                     (cfg CFG-LABEL_1 (BB_1 ...))
                     (cfg CFG-LABEL_after (BB_after ...)) ...)
                    CFG-LABEL_1)
   (cfg CFG-LABEL_1 (BB_1 ...))])

(define-metafunction IPPC
  lookup-basic-block : CFG BB-LABEL -> BB
  [(lookup-basic-block (cfg CFG-LABEL_1 
                            ((basic-block BB-LABEL_before INSTRS_before CONTROL-OP_before) ...
                             (basic-block BB-LABEL_1 INSTRS_1 CONTROL-OP_1)
                             (basic-block BB-LABEL_after INSTRS_after CONTROL-OP_after) ...))
                       BB-LABEL_1)
   (basic-block BB-LABEL_1 INSTRS_1 CONTROL-OP_1)])

(define (symbol-of-mv mv)
  (match mv
    [`(,symb ,v) symb]))

(define (mv-var? mv)
  (eq? (symbol-of-mv mv) `mv-var))

(define-metafunction IPPC
  lookup-frame-variable : (ARG ...) VAR -> MACHINE-VAL
  [(lookup-frame-variable ((VAR_before MACHINE-VAL_before) ...
                           (VAR_1 MACHINE-VAL_1)
                           (VAR_after MACHINE-VAL_after) ...)
                          VAR_1)
   MACHINE-VAL_1
   (side-condition (not (mv-var? (term MACHINE-VAL_1))))]
  [(lookup-frame-variable ((VAR_before MACHINE-VAL_before) ...
                           (VAR_1 MACHINE-VAL_1)
                           (VAR_after MACHINE-VAL_after) ...)
                          VAR_1)
   (lookup-frame-variable ((VAR_before MACHINE-VAL_before) ...
                           (VAR_1 MACHINE-VAL_1)
                           (VAR_after MACHINE-VAL_after) ...)
                          VAR_2)
   (where (mv-var VAR_2) MACHINE-VAL_1)])

(define-metafunction IPPC
  resolve-machine-val : (ARG ...) MACHINE-VAL -> MACHINE-VAL
  [(resolve-machine-val (ARG_1 ...) (mv-number number_1)) (mv-number number_1)]
  [(resolve-machine-val (ARG_1 ...) (mv-csl number_1)) (mv-csl number_1)]
  [(resolve-machine-val (ARG_1 ...) (mv-ipfs-hash number_1)) (mv-ipfs-hash number_1)]
  [(resolve-machine-val (ARG_1 ...) (mv-var VAR_1)) (lookup-frame-variable (ARG_1 ...) VAR_1)])

(define-metafunction IPPC
  resolve-machine-vals : (ARG ...) (MACHINE-VAL ...) -> (MACHINE-VAL ...)
  [(resolve-machine-vals (ARG_1 ...) (MACHINE-VAL_1 ...))
   ((resolve-machine-val (ARG_1 ...) MACHINE-VAL_1) ...)])

(define-metafunction IPPC
  resolve-arg : (ARG ...) ARG -> ARG
  [(resolve-arg (ARG_1 ...) (VAR_1 MACHINE-VAL_1))
   (VAR_1 (resolve-machine-val (ARG_1 ...) MACHINE-VAL_1))])

(define-metafunction IPPC
  force-machine-number : MACHINE-VAL -> number
  [(force-machine-number (mv-number number_1)) number_1])

(define-metafunction IPPC
  resolve-machine-val-to-number : (ARG ...) MACHINE-VAL -> number
  [(resolve-machine-val-to-number (ARG_1 ...) MACHINE-VAL_1)
   (force-machine-number (resolve-machine-val (ARG_1 ...) MACHINE-VAL_1))])
                                              
(define (op-of-symbol symb)
  (match symb
    [`+ +]
    [`- -]
    [`* *]
    [`/ /]))

(define -->thread
  (reduction-relation
   IPPC #:domain THREAD

   (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f TRAMPOLINE_f ARG_1 ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_f ((arith VAR_f OP_f MACHINE-VAL_arith ...) INSTR_f ...)
                             CONTROL-OP_f))
        (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f TRAMPOLINE_f ARG_1 ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                (basic-block BB-LABEL_f ((frame-store VAR_f (mv-number number_res)) INSTR_f ...)
                             CONTROL-OP_f))
        (side-condition (> (term FUEL_1) 0))
        (where number_res ,(apply (op-of-symbol (term OP_f)) (term ((resolve-machine-val-to-number (ARG_1 ...) MACHINE-VAL_arith) ...))))
        thread-arith)
      
   (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f TRAMPOLINE_f ARG_f ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_f ((frame-store VAR_f MACHINE-VAL_f2) INSTR_f ...)
                             CONTROL-OP_f))
        (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f TRAMPOLINE_f ARG_f ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                (basic-block BB-LABEL_f (INSTR_f ...)
                             CONTROL-OP_f))
        (side-condition (> (term FUEL_1) 0))
        thread-frame-store-hd)

   (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_fpred BB-LABEL_fsucc) ARG_f ...) FRAME_fafter ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_1 ()
                             (jump BB-LABEL_2)))
        (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_fsucc BB-LABEL_2) ARG_f ...)
                       FRAME_fafter ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                BB_entry)
        (where CFG_fr (lookup-function PROGRAM_1 CFG-LABEL_f))
        (where BB_entry (lookup-basic-block CFG_fr BB-LABEL_2))
        (side-condition (> (term FUEL_1) 0))
        thread-jump)

   (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_fpred BB-LABEL_fsucc) ARG_f ...) FRAME_fafter ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_1 ()
                             (conditional-jump MACHINE-VAL_tgt BB-LABEL_2 ...)))
        (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_fsucc BB-LABEL_3) ARG_f ...)
                       FRAME_fafter ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                BB_entry)
        (where number_bb (resolve-machine-val-to-number (ARG_f ...) MACHINE-VAL_tgt))
        (where BB-LABEL_3 ,(list-ref (term (BB-LABEL_2 ...)) (term number_bb)))
        (where CFG_fr (lookup-function PROGRAM_1 CFG-LABEL_f))
        (where BB_entry (lookup-basic-block CFG_fr BB-LABEL_3))
        (side-condition (> (term FUEL_1) 0))
        thread-conditional-jump)

   (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_pred BB-LABEL_succ) ARG_f ...) FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_1 ()
                             (call CFG-LABEL_g BB-LABEL_retg ARG_g ...)))
        (thread (stack (frame ACTIVATION-ID_g  CFG-LABEL_g ((entry-label) (return-label)) (resolve-arg (ARG_f ...) ARG_g) ...)
                       (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_pred BB-LABEL_retg) ARG_f ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                BB_entry)
        (where CFG_gr (lookup-function PROGRAM_1 CFG-LABEL_g))
        (where BB_entry (lookup-basic-block CFG_gr (entry-label)))
        (fresh ACTIVATION-ID_g)
        (side-condition (> (term FUEL_1) 0))
        thread-call)

  (--> (thread (stack (frame ACTIVATION-ID_f CFG-LABEL_f (BB-LABEL_fpred BB-LABEL_fsucc) ARG_f ...)
                      (frame ACTIVATION-ID_g CFG-LABEL_g (BB-LABEL_gpred BB-LABEL_gsucc) ARG_g ...) FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                FUEL_1
                (basic-block BB-LABEL_1 ()
                             (return)))
       (thread (stack (frame ACTIVATION-ID_g CFG-LABEL_g (BB-LABEL_gsucc BB-LABEL_gsucc) ARG_g ...) FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                ,(sub1 (term FUEL_1))
                BB_gret)
       (where CFG_gr (lookup-function PROGRAM_1 CFG-LABEL_g))
       (where BB_gret (lookup-basic-block CFG_gr BB-LABEL_gsucc))
       (side-condition (> (term FUEL_1) 0))
       thread-return)
  
  ))

(define bb1
  (term
   (basic-block (entry-label) () (call bar lab3 (x (mv-number 23))))))

(define cfg1
  (term
    (cfg foo
         (,bb1
          (basic-block lab3 () (jump lab32))))))

(define cfg2
  (term
    (cfg bar
         ((basic-block (entry-label) () (return))))))

(define thread1
  (term
   (thread (stack (frame ACTIVATION-ID_g foo ((entry-label) lsucc) (x (mv-number 1))))
           ()
           (program ,cfg1 ,cfg2)
           10
           ,bb1)))

(define thread2
  (term
   (thread
    (stack (frame tttg bar ((entry-label) (return-label)) (x (mv-number 23))) (frame x123 foo ((entry-label) lab3) (x (mv-number 1))))
    ()
    (program
     (cfg foo ((basic-block (entry-label) () (call bar lab3 (x (mv-number 23)))) (basic-block lab3 () (jump lab32))))
     (cfg bar ((basic-block (entry-label) () (return)))))
    33
    (basic-block (entry-label) () (return)))))

(define thread3
  (term
   (thread
    (stack (frame xxxg bar ((entry-label) (return-label)) (x (mv-number 23))) (frame x123 foo ((entry-label) lab3) (x (mv-number 1))))
    ()
    (program
     (cfg foo ((basic-block (entry-label) () (call bar lab3 (x (mv-number 23)))) (basic-block lab3 () (jump lab32))))
     (cfg bar ((basic-block (entry-label) () (return)))))
    8
    (basic-block (entry-label) ((frame-store x (mv-number 3232))) (return)))))

(define thread4
  (term
   (thread
    (stack (frame xxxg bar ((entry-label) (return-label)) (x (mv-number 23))) (frame x123 foo ((entry-label) lab3) (x (mv-number 1))))
    ()
    (program
     (cfg foo ((basic-block (entry-label) () (call bar lab3 (x (mv-number 23)))) (basic-block lab3 () (jump lab32))))
     (cfg bar ((basic-block (entry-label) () (return)))))
    8
    (basic-block (entry-label) ((arith x + (mv-number 1) (mv-number 3232))) (return)))))

(define thread5
  (term
   (thread
   (stack (frame xxxg bar ((entry-label) (return-label)) (x (mv-number 23))) (frame x123 foo ((entry-label) lab3) (x (mv-number 1))))
   ()
   (program
    (cfg foo ((basic-block (entry-label) () (call bar lab3 (x (mv-number 23)))) (basic-block lab3 () (jump lab32))))
    (cfg bar ((basic-block (entry-label) () (return)))))
   7
   (basic-block (entry-label) ((frame-store x (mv-number 3233))) (return)))))

(define thread6
  (term
   (thread
   (stack (frame xxxg bar ((entry-label) (return-label)) (x (mv-number 23))) (frame x123 foo ((entry-label) lab3) (x (mv-number 1))))
   ()
   (program
    (cfg foo ((basic-block (entry-label) () (call bar lab3 (x (mv-number 23)))) (basic-block lab3 () (jump lab32))))
    (cfg bar ((basic-block (entry-label) () (return)))))
   7
   (basic-block (entry-label) () (conditional-jump (mv-number 0) (entry-label))))))