#lang racket
(require redex)

(define-language ippc
  (T ::= int (* T) (→ T T ...))
  (x ::= variable-not-otherwise-mentioned)
  (l ::= number)
  (⋄ ::= ~ !)
  (⊙ ::= + - && || ==)
  (e ::= number x (⋄ e) (⊙ e e) (cread e e))
  (s ::=
     (:= x e)
     (:= x e e ...)
     (:= x new (x s))
     (delete e)
     (cond (e e) ...)
     (return e))
  (f ::= (T x))
  (d ::= (T x (f ...) (f ...) s))
  (p ::= (d ...)))

(define-extended-language ippc-machine ippc
  (v ::= number l garbage)
  (ρ ::= ((x v) ...))
  (c ::= (v ...))
  (μ ::= ((l c) ...))
  (κ ::= ε (number (s ...) x ρ κ))
  (σ ::= ((s ...) x κ ρ μ p)))

(define-metafunction ippc-machine
  val : e ρ μ -> v
  [(val number_1 ρ_1 μ_1) number_1]
  [(val x_t ((x_1 v_1) ... (x_t v_t) (x_n v_n) ...) μ_1) v_t]
  [(val (~ e_1) ρ_1 μ_1) ,(- (term (val e_1 ρ_1 μ_1)))]
  [(val (! e_1) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 0) 1 0)]
  [(val (+ e_1 e_2) ρ_1 μ_1) ,(+ (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1)))]
  [(val (- e_1 e_2) ρ_1 μ_1) ,(- (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1)))]
  [(val (&& e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 1) (term (val e_2 ρ_1 μ_1)) 0)]
  [(val (|| e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 0) (term (val e_2 ρ_1 μ_1)) 1)]
  [(val (== e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1))) 1 0)]
  [(val (cread e_1 e_2) ρ_1 μ_1) ,(list-ref (term c_1) (term v_2))
                                 (where l_1 (val e_1 ρ_1 μ_1))
                                 (where v_2 (val e_2 ρ_1 μ_1))
                                 (side-condition (number? (term v_2)))
                                 (where ((l_b c_b) ... (l_1 c_1) (l_a c_a) ...) μ_1)])
                      
; (redex-match? ippc d (term (int foo ((int z)) ((int yy)) (:= yy bar (+ z 2)))))