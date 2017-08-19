#lang racket
(require redex)

(define-language IPPC
  (THD ::= (S CS PROG)) ; thread
  (S ::= (stack F ...)) ; stack
  (F ::= (frame FL T MV ...)) ; frame
  (T ::= (LB LB)) ; trampoline (pred, succ)
  (MV ::= number CSL) ; machine value

  (CS ::= ((CSL C) ...)) ; chunk store
  (C ::= (chunk MV ...)) ; chunk
  (CSL ::= number) ; chunk-store location
  
  (PROG (CFG ...)) ; program
  (CFG ::= (FL F (BB ...))) ; function (as CFG)
  (BB ::= (LB IS)) ; basic block
  (IS ::= (I ...))
  (I ::= ; instruction
     (let ((VAR (O V ...))))
     (O V ...))
  (O ::=
     add1 sub1 + *
     chunk-alloc chunk-free
     chunk-read chunk-write
     frame-read frame-write)
  (V ::=
     VAR number)

  (LB ::= variable-not-otherwise-mentioned) ; basic-block label
  (FL ::= variable-not-otherwise-mentioned) ; function label
  (VAR ::= variable-not-otherwise-mentioned)) ; variable

(define-metafunction IPPC
  lookup-basic-block : (BB ...) LB -> IS
  [(lookup-basic-block ((LB_before IS_before) ... (LB_1 IS_1) (LB_after IS_after) ...) LB_1)
   IS_1]
  [(lookup-basic-block ((LB_before IS_before) ...) LB_1)
   ()])