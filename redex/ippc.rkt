#lang racket
(require redex)

(define-language IPPC
  (THREAD ::= (thread STACK CHUNK-STORE PROGRAM BB))
  (STACK ::= (stack FRAME ...))
  (FRAME ::= (frame CFG-LABEL TRAMPOLINE ARG ...)) ; stack frame
  (ARG ::= (VAR MACHINE-VALUE)) ; function argument
  (TRAMPOLINE ::= (BB-LABEL BB-LABEL)) ; the trampoline consists of a pair
                                       ; of basic-block labels, namely
                                       ;  (predecessor, successor)
                                       ; where predecessor refers to the current
                                       ; basic block and successor to the next one.
  (MACHINE-VALUE ::= LITERAL CHUNK-STORE-LOCATION IPFS-HASH)
  (IPFS-HASH ::= (hash number))

  (CHUNK-STORE ::= ((CHUNK-STORE-LOCATION CHUNK) ...))
  (CHUNK-STORE-LOCATION ::= number)
  (CHUNK ::= ; every chunk is represented by a chunk object
             ; and its associated header object.
             ; the header object stores a pointer to its
             ; chunk object and optionally the ipfs hash
             ; code of the chunk object.
         (chunk-header CHUNK-STORE-LOCATION IPFS-HASH ...)
         (chunk MACHINE-VALUE ...))
  
  (PROGRAM ::= (program CFG ...))
  (CFG ::= (cfg CFG-LABEL (BB ...))) ; function (represented by control-flow graph)
  (BB ::= (basic-block BB-LABEL INSTRS CONTROL-OP)) ; basic block
  (CONTROL-OP ::=
              (jump BB-LABEL)
              (conditional-jump OPERAND BB-LABEL ...) ; (conditional-jump i lab ...)
                                                      ; jump to ith basic-block label in lab ...
              (call CFG-LABEL BB-LABEL (VAR MACHINE-VALUE) ...)   ; (call f lab args ...)
                                                                  ; call function f passing argument list
                                                                  ; args ..., and upon return jumping to
                                                                  ; basic block with label lab
              (return))
  (INSTRS ::= (INSTR ...))
  (INSTR ::= (OP OPERAND ...))
  (OP ::=
     chunk-alloc chunk-free
     chunk-store frame-store)
  (OPERAND ::=
       MACHINE-VALUE
       VAR ; lookup value in the frame
       (chunk-load OPERAND OPERAND)) ; (chunk-read c i)
                                     ; load value from position i in chunk c
       
  (LITERAL ::= number IPFS-HASH)
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

(define-metafunction IPPC
  lookup-frame-variable : FRAME VAR -> MACHINE-VALUE
  [(lookup-frame-variable (frame CFG-LABEL_1 TRAMPOLINE_1
                                 (VAR_before MACHINE-VALUE_before) ...
                                 (VAR_1 MACHINE-VALUE_1)
                                 (VAR_after MACHINE-VALUE_after) ...)
                          VAR_1)
   MACHINE-VALUE_1])

(define bb1
  (term
   (basic-block (entry-label) () (call foo (return-label)))))

(define cfg1
  (term
    (cfg foo
         (,bb1
          (basic-block lab3 () (jump lab32))))))

(define thread1
  (term
   (thread (stack (frame foo ((entry-label) lsucc) (x 1)))
           ()
           (program ,cfg1)
           ,bb1)))

(define prob
  (term
   (thread (stack (frame foo ((entry-label) ((return-label))))
                  (frame foo ((entry-label) (return-label)) (x 1)))
           ()
           (program (cfg foo ((basic-block (entry-label) () (call foo (return-label))) (basic-block lab3 () (jump lab32)))))
           (basic-block (entry-label) () (call foo (return-label))))))

(define -->thread
  (reduction-relation
   IPPC #:domain THREAD

   (--> (thread (stack (frame CFG-LABEL_f (BB-LABEL_pred BB-LABEL_succ) ARG_f ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                (basic-block BB-LABEL_1 () (call CFG-LABEL_g BB-LABEL_retg ARG_g ...)))
        (thread (stack (frame CFG-LABEL_g ((entry-label) (return-label)) ARG_g ...)
                       (frame CFG-LABEL_f (BB-LABEL_pred BB-LABEL_retg) ARG_f ...)
                       FRAME_after ...)
                CHUNK-STORE_1
                PROGRAM_1
                BB_entry)
        (where CFG_fr (lookup-function PROGRAM_1 CFG-LABEL_f))
        (where BB_entry (lookup-basic-block CFG_fr (entry-label)))
        thread-call)))
               