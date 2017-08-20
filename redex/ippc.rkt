#lang racket
(require redex)

(define-language IPPC
  (THREAD ::= (STACK CHUNK-STORE PROGRAM)) ; thread
  (STACK ::= (stack FRAME ...)) ; stack
  (FRAME ::= (frame CFG-LABEL TRAMPOLINE (VAR MACHINE-VALUE) ...)) ; frame
  (TRAMPOLINE ::= (BB-LABEL BB-LABEL)) ; trampoline: (pred, succ)
  (MACHINE-VALUE ::= LITERAL CHUNK-STORE-LOCATION) ; machine value

  (CHUNK-STORE ::= ((CHUNK-STORE-LOCATION CHUNK) ...)) ; chunk store
  (CHUNK ::=
         (chunk-header CHUNK-STORE-LOCATION HASH ...)
         (chunk MACHINE-VALUE ...))
  (CHUNK-STORE-LOCATION ::= number) ; chunk-store location
  (HASH ::= (hash number)) ; ipfs hash value
  
  (PROGRAM ::= (program CFG ...)) ; whole program
  (CFG ::= (cfg CFG-LABEL FRAME (BB ...))) ; function (as CFG)
  (BB ::= (BB-LABEL INSTRS CONTROL-OP)) ; basic block
  (CONTROL-OP ::=
              (jump BB-LABEL)
              (conditional-jump OPERAND BB-LABEL ...) ; (conditional-jump i lab ...)
                                                      ; jump to ith basic-block label in lab ...
              (call CFG-LABEL BB-LABEL OPERAND ...))  ; (call f lab args ...)
                                                      ; call function f passing argument list
                                                      ; args ..., and upon return jumping to
                                                      ; basic block with label lab
  (INSTRS ::= (INSTR ...))
  (INSTR ::= ; instruction
     (OP OPERAND ...))
  (OP ::=
     chunk-alloc chunk-free
     chunk-store frame-store)
  (OPERAND ::=
       MACHINE-VALUE
       VAR ; lookup value in the frame
       (chunk-load OPERAND OPERAND)) ; (chunk-read c i)
                                     ; load value from position i in chunk c
       
  (LITERAL ::= number HASH)
  (BB-LABEL ::= variable-not-otherwise-mentioned) ; basic-block label
  (CFG-LABEL ::= variable-not-otherwise-mentioned) ; CFG/function label
  (VAR ::= variable-not-otherwise-mentioned)) ; variable

(define-metafunction IPPC
  lookup-basic-block : (BB ...) BB-LABEL -> INSTRS
  [(lookup-basic-block ((BB-LABEL_before INSTRS_before) ... (BB-LABEL_1 INSTRS_1) (BB-LABEL_after INSTRS_after) ...) BB-LABEL_1)
   INSTRS_1]
  [(lookup-basic-block ((BB-LABEL_before INSTRS_before) ...) BB-LABEL_1)
   ()])

(define-metafunction IPPC
  lookup-frame-variable : FRAME VAR -> MACHINE-VALUE
  [(lookup-frame-variable (frame CFG-LABEL_1 TRAMPOLINE_1 (VAR_before MACHINE-VALUE_before) ... (VAR_1 MACHINE-VALUE_1) (VAR_after MACHINE-VALUE_after) ...) VAR_1)
   MACHINE-VALUE_1])