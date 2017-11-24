#lang racket
(require redex)

; http://siek.blogspot.fr/2012/07/the-semantics-of-familiar-language.html

(define-language ippc
  (T ::= int (* T) (→ T T ...))
  (x ::= variable-not-otherwise-mentioned)
  (l := variable-not-otherwise-mentioned)
  (i ::= number)
  (⋄ ::= ~ !)
  (⊙ ::= + - && || ==)
  (e ::= number x (⋄ e) (⊙ e e) (chunk-read e e))
  (s ::=
     (:= x l e e ...)
     (:= x new (x s))
     (delete e)
     (label l s)
     (if-goto e l)
     (return e))
  (f ::= (T x))
  (d ::= (T x (f ...) (f ...) (s ...)))
  (p ::= (d ...)))

(define-extended-language ippc-machine ippc
  (v ::= number i (garbage))
  (ρ ::= ((x v) ...))
  (c ::= (v ...))
  (μ ::= ((i c) ...))
  (κ ::= ε (l (s ...) x ρ κ))
  (σ ::= ((s ...) x κ ρ μ p))
  (m ::= (ρ σ)))

(define-metafunction ippc-machine
  val : e ρ ρ μ -> v
  [(val number_1 ρ_1 ρ_2 μ_1) number_1]
  [(val x_t ρ_1 ρ_2 μ_1) v_t
                         (where ((x_1 v_1) ... (x_t v_t) (x_n v_n) ...) ρ_1)]
  [(val x_t ρ_1 ρ_2 μ_1) v_t
                         (where ((x_1 v_1) ... (x_t v_t) (x_n v_n) ...) ρ_2)
                         (side-condition (not (assoc (term x_t) (term ρ_1))))]
  [(val (~ e_1) ρ_1 ρ_2 μ_1) ,(- (term (val e_1 ρ_1 ρ_2 μ_1)))]
  [(val (! e_1) ρ_1 ρ_2 μ_1) ,(if (= (term (val e_1 ρ_1 ρ_2 μ_1)) 0) 1 0)]
  [(val (+ e_1 e_2) ρ_1 ρ_2 μ_1) ,(+ (term (val e_1 ρ_1 ρ_2 μ_1)) (term (val e_2 ρ_1 ρ_2 μ_1)))]
  [(val (- e_1 e_2) ρ_1 ρ_2 μ_1) ,(- (term (val e_1 ρ_1 ρ_2 μ_1)) (term (val e_2 ρ_1 ρ_2 μ_1)))]
  [(val (&& e_1 e_2) ρ_1 ρ_2 μ_1) ,(if (= (term (val e_1 ρ_1 ρ_2 μ_1)) 1) (term (val e_2 ρ_1 ρ_2 μ_1)) 0)]
  [(val (|| e_1 e_2) ρ_1 ρ_2 μ_1) ,(if (= (term (val e_1 ρ_1 ρ_2 μ_1)) 0) (term (val e_2 ρ_1 ρ_2 μ_1)) 1)]
  [(val (== e_1 e_2) ρ_1 ρ_2 μ_1) ,(if (= (term (val e_1 ρ_1 ρ_2 μ_1)) (term (val e_2 ρ_1 ρ_2 μ_1))) 1 0)]
  [(val (chunk-read e_1 e_2) ρ_1 ρ_2 μ_1) ,(list-ref (term c_1) (term v_2))
                                      (where i_1 (val e_1 ρ_1 ρ_2 μ_1))
                                      (where v_2 (val e_2 ρ_1 ρ_2 μ_1))
                                      (side-condition (number? (term v_2)))
                                      (where ((i_b c_b) ... (i_1 c_1) (i_a c_a) ...) μ_1)])

(define (symbol-of-statement s)
  (match s
    [`(,symb ,v) symb]))

(define (goto? s)
  (eq? (symbol-of-statement s) `label))

(define-metafunction ippc
  goto : l (s ...) -> (s ...)
  [(goto l_1 ((label l_1 s_0) s_1 ...))
   (s_0 s_1 ...)]
  [(goto l_1 ((label l_2 s_0) s_1 ...))
   (goto l_1 (s_0 s_1 ...))
   (side-condition (not (eq? (term l_1) (term l_2))))]
  [(goto l_1 (s_0 s_1 ...))
   (goto l_1 (s_1 ...))
   (side-condition (not (goto? (term s_0))))])

(define-metafunction ippc
  get-function : x p -> d
  [(get-function x_1 ((T_1 x_1 (f_1 ...) (f_2 ...) (s_b ...)) d_1 ...))
   (T_1 x_1 (f_1 ...) (f_2 ...) (s_b ...))]
  [(get-function x_1 ((T_1 x_2 (f_1 ...) (f_2 ...) s_b) d_1 ...))
   (get-function x_1 (d_1 ...))
   (side-condition (not (eq? (term x_1) (term x_2))))])

(define-metafunction ippc
  get-function-body : x p -> (s ...)
  [(get-function-body x_1 (d_1 ...))
   (s_b ...)
   (where (T_1 x_1 (f_1 ...) (f_2 ...) (s_b ...)) (get-function x_1 (d_1 ...)))])

(define ⟶
  (reduction-relation
   ippc-machine #:domain m

   (--> ((ρ_11 ... (x_a v_a0) ρ_12 ...) (((:= x_a e_a) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        ((ρ_11 ... (x_a v_a) ρ_12 ...) ((s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (where v_a (val e_a (ρ_11 ... (x_a v_a0) ρ_12 ...) ρ_2 μ_1))
        "assignment")

   (--> (ρ_1 (((label l_1 s_0) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (ρ_1 ((s_0 s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        "label")

   (--> (ρ_1 (((if-goto e_1 l_1) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (ρ_1 ((s_t ...) x_f κ_1 ρ_2 μ_1 p_1))
        (side-condition (eq? (term (val e_1 ρ_1 ρ_2 μ_1)) 1))
        (where (s_t ...) (goto l_1 (get-function-body x_f p_1)))
        "if-goto-true")

   (--> (ρ_1 (((if-goto e_1 l_1) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (ρ_1 ((s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (side-condition (eq? (term (val e_1 ρ_1 ρ_2 μ_1)) 0))
        "if-goto-false")

   (--> (ρ_1 (((:= x_a l_ret e_g e_args ...) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
        (ρ_1 ((s_g ...) x_g κ_g ρ_g μ_1 p_1))
        (where x_g (val e_g ρ_1 ρ_2 μ_1))
        (where (v_args ...) ((val e_args ρ_1 ρ_2 μ_1) ...))
        (where (T_g x_g0 ((T_g2 x_g2) ...) ((T_g3 x_g3) ...) (s_g ...)) (get-function x_g p_1))
        (where ρ_g ((x_g2 v_args) ... (x_g3 (garbage)) ...))
        (where κ_g (l_ret (s_1 ...) x_g ρ_2 κ_1))
        "call")

   (--> (ρ_1 (((return e_1) s_1 ...) x_g (l_ret (s_f ...) x_f ρ_f κ_1) ρ_2 μ_1 p_1))
        (ρ_1 ((s_ret ...) x_f (l_ret (s_f ...) x_f ρ_f2 κ_1) ρ_2 μ_1 p_1))
        (where v_1 (val e_1 ρ_1 ρ_2 μ_1))
        (where (((:= x_a l_ret0 e_g0 e_args0 ...)) s_ret ...) (goto l_ret (get-function-body x_f p_1)))
        (where ((x_f1 v_a1) ... (x_a v_a0) (x_f2 v_a2) ...) ρ_f)
        (where ρ_f2 ((x_f1 v_a1) ... (x_a v_1) (x_f2 v_a2) ...))
        "return")
        
   ))
   
; (redex-match? ippc d (term (int foo ((int z)) ((int yy)) (:= yy bar (+ z 2)))))