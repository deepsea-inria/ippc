#lang racket
(require redex)
(require file/sha1)

; Language definition
; -------------------

(define-language ippc
  (T ::= int (* T) (→ T T ...)) ; types
  (x ::= variable-not-otherwise-mentioned) ; variables
  (l ::= variable-not-otherwise-mentioned) ; labels
  (⋄ ::= ~ !) ; unary operators
  (⊙ ::= + - && || ==) ; binary operators
  (e ::= number x (⋄ e) (⊙ e e) (chunk-read e e)) ; expressions
  (s ::= ; statements
     (:= x x e e ...) ; function calls
     (label l s) ; labels
     (if-goto e l) ; conditionals
     (return e) ; returns
     (fork-join s s) ; fork-join calls
     (:= x (chunk-new e e)) ; chunk allocations
     (chunk-delete e) ; chunk deallocations
     (chunk-write e e e)) ; chunk writes
  (f ::= (T x)) ; function-declaration headers
  (d ::= (T x (f ...) (f ...) (s ...))) ; function declarations
  (p ::= (d ...))) ; programs

; Support for chunks
; ------------------

(define-extended-language ippc-chunk ippc
  (i ::= variable-not-otherwise-mentioned) ; chunk-heap locations
  (h ::= string) ; hash codes
  (v ::= (garbage) number i h) ; values
  (chdr ::= (chdr-fresh) (chdr-owner h) (chdr-copy h)) ; chunk headers
  ; - (chdr-fresh) indicates the chunk is not promoted (yet)
  ; - (chdr-owner h) indicates the chunk is promoted, it is owned by the node, and its hash is h
  ; - (chdr-copy h) indicates the chunk is promoted, it is a cached copy, and its hash is h
  (c ::= (chdr v ...)) ; chunks
  (μ ::= ((i c) ...)) ; chunk heaps
  (cur ::= (i h) ((i ...) (h ...) cur)) ; chunk-heap-traversal cursors
  ; - ε empty cursor
  ; - (v ...) list of values to be processed
  ; - (h ...) list of hash values of promoted chunks
  ; - cur the remaining part of the cursor
  (wl ::= (cur ...)) ; chunk-heap-traversal worklists
  (η ::= ((h c) ...))) ; ipfs heaps

; Support for threads
; -------------------
  
(define-extended-language ippc-thread ippc-chunk
  (tid ::= variable-not-otherwise-mentioned) ; thread id
  (ρ ::= ((x v) ...)) ; environments (i.e., frames)
  (flk ::= (par) (seq)) ; frame linkage types
  ; - par indicates that the frame represents the right branch of a fork join
  ; - seq for all other frames
  (κ ::= ε (l (s ...) x ρ flk κ)) ; call stacks
  ;   - l label of current block
  ;   - (s ...) list of statements to be performed in order
  ;   - x name of the current function
  ;   - ρ environment of the current function
  ;   - κ stack of the current function
  (fuel ::= number) ; fuel to power chunk-promotion work
  (σ ::= ((s ...) x ρ κ fuel wl p)) ; sequential-machine states
  ;   - (s ...) list of statements to be performed in order
  ;   - x name of the current function
  ;   - ρ environment of the current function
  ;   - κ call stack
  ;   - fuel count of nb. machine steps remaining until promotion
  ;   - wl work list (zipper representation) of the frontier of chunk promotion
  ;   - p copy of the program text
  (thd ::= (tid σ  number (tid ...)))) ; thread states
  ; - tid unique id of the thread
  ; - σ sequential-machine state
  ; - number the number of incoming thread dependencies
  ; - (tid ...) set of ids of the outgoing thread dependencies

; The abstract machine structure
; ------------------------------

(define-extended-language ippc-machine ippc-thread
  (msg ::= (thd-decr tid) (chk-del h)) ; intra-node messages
  ; - (thd-decr tid) to decrement the number of incoming dependencies of thread tid
  ; - (chk-del h) to free the memory associated with the chunk associated with hash code h
  (mbx ::= (msg ...)) ; node mailboxes
  (n ::= ((σ ...) (σ ...) μ η mbx)) ; nodes
  ; - (σ ...) set of ready threads
  ; - (σ ...) set of blocked threads
  ; - μ chunk heap
  ; - mbx mailbox
  (m ::= (n ...))) ; machine states

; Metafunctions for hashing
; -------------------------

(define bytes->hash
  (lambda (bs)
    (sha1 (open-input-bytes bs))))

(define hash->bytes
  (lambda (h)
    (bytes->list (string->bytes/utf-8 h))))

(define number->hash
  (lambda (n)
    (bytes->hash (string->bytes/utf-8 (number->string n)))))

(define hash-combine
  (lambda (h1 h2)
    (bytes->hash (list->bytes (map + (hash->bytes h1) (hash->bytes h2))))))

(define nullary-hash
  (bytes->hash (list->bytes '())))

(define list->hash
  (lambda (hs)
    (foldl hash-combine nullary-hash hs)))

(define-metafunction ippc-chunk
  Numbers->hash : number ... -> h
  [(Numbers->hash number_1 ...) ,(list->hash (map number->hash (term (number_1 ...))))])

(define-metafunction ippc-chunk
  Chunk-contents->hash : variable (number ...) -> h
  [(Chunk-contents->hash variable_1 (number_1 ...))
   (hash-combine h_1 (bytes->hash (string->bytes/utf-8 (symbol->string variable_1))))
   (where h_1 (Numbers->hash number_1 ...))])

(define-metafunction ippc-chunk
  List->hash : h ... -> h
  [(List->hash h_1 ...) ,(list->hash (term (h_1 ...)))])
   
; Metafunctions for chunks
; ------------------------

(define-metafunction ippc-chunk
  Make-chunk-owner : h c -> c
  [(Make-chunk-owner h_1 ((chdr-fresh) v_1 ...))
   ((chdr-owner h_1) v_1 ...)]
  [(Make-chunk-owner h_1 (chdr_1 v_1 ...))
   (chdr_1 v_1 ...)
   (side-condition (not (equal? (term chdr_1) (term (chdr-fresh)))))])

(define-metafunction ippc-chunk
  Make-chunk-copy : h c -> c
  [(Make-chunk-copy h_1 ((chdr-fresh) v_1 ...))
   ((chdr-copy h_1) v_1 ...)]
  [(Make-chunk-copy h_1 (chdr_1 v_1 ...))
   (chdr_1 v_1 ...)
   (side-condition (not (equal? (term chdr_1) (term (chdr-fresh)))))])

(define-metafunction ippc-chunk
  Chdr->hash : chdr -> h
  [(Chdr->hash (chdr-owner h_1)) h_1]
  [(Chdr->hash (chdr-copy h_1)) h_1])

(define-metafunction ippc-chunk
  Promote-step : (cur μ η) -> (cur μ η)
  ; promote a leaf-level chunk
  [(Promote-step (((i_1 i_2 ...) (h_2 ...) cur_1) ((i_b c_b) ... (i_1 ((chdr-fresh) number_1 ...)) (i_a c_a) ...) ((h_h c_h) ...)))
   (((i_2 ...) (h_1 h_2 ...) cur_1) ((i_b c_b) ... (i_1 c_1) (i_a c_a) ...) ((h_h c_h) ... (h_1 c_1)))
   (where h_1 (Chunk-contents->hash i_1 (number_1 ...)))
   (where c_1 (Make-chunk-owner h_1 ((chdr-fresh) number_1 ...)))]
  ; start promoting an interior chunk
  [(Promote-step (((i_1 i_2 ...) (h_2 ...) cur_1) ((i_b c_b) ... (i_1 ((chdr-fresh) i_n ...)) (i_a c_a) ...) η_1))
   (cur_2 ((i_b c_b) ... (i_1 ((chdr-fresh) i_n ...)) (i_a c_a) ...) η_1)
   (where cur_2 ((i_n ...) () ((i_1 i_2 ...) (h_2 ...) cur_1)))]
  ; reached a chunk that is already promoted
  [(Promote-step (((i_1 i_2 ...) (h_2 ...) cur_1) ((i_b c_b) ... (i_1 (chdr_1 v_n ...)) (i_a c_a) ...) η_1))
   (((i_2 ...) (h_1 h_2 ...) cur_1) ((i_b c_b) ... (i_1 (chdr_1 v_n ...)) (i_a c_a) ...) η_1)
   (side-condition (not (equal? (term chdr_1) (term (chdr-fresh)))))
   (where h_1 (Chdr->hash chdr_1))]
  ; reached the end of the promotion
  [(Promote-step ((() (h_2 ...) (i_1 h_1)) μ_1 η_1))
   ((i_1 h_3) μ_1 η_1)
   (where h_3 (List->hash ,(reverse (term (h_2 ...)))))]
  ; pop the promotion stack
  [(Promote-step ((() (h_1 ...) ((i_1 i_2 ...) (h_2 ...) cur_1)) ((i_b c_b) ... (i_1 c_1) (i_a c_a) ...) ((h_4 c_4) ...)))
   (((i_2 ...) (h_3 h_2 ...) cur_1) ((i_b c_b) ... (i_1 c_2) (i_a c_a) ...) ((h_4 c_4) ... (h_3 c_2)))
   (where c_2 (Make-chunk-owner h_3 c_1))
   (where h_3 (List->hash ,(reverse (term (h_1 ...)))))])

(define-metafunction ippc-chunk
  Chunk-read : c number -> v
  [(Chunk-read (chdr_1 v_1 ...) number_1) ,(list-ref (term (v_1 ...)) (term number_1))])

; Metafunctions for evaluation of expressions
; -------------------------------------------

; Evaluates an expression e to a value v in the environment
; ρ with chunk heap μ. The result is the value v.
(define-metafunction ippc-machine
  val : e ρ μ -> v
  [(val number_1 ρ_1  μ_1) number_1]
  [(val x_t ρ_1  μ_1) v_t
                      (where ((x_1 v_1) ... (x_t v_t) (x_n v_n) ...) ρ_1)]
  [(val (~ e_1) ρ_1 μ_1) ,(- (term (val e_1 ρ_1 μ_1)))]
  [(val (! e_1) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 0) 1 0)]
  [(val (+ e_1 e_2) ρ_1 μ_1) ,(+ (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1)))]
  [(val (- e_1 e_2) ρ_1 μ_1) ,(- (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1)))]
  [(val (&& e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 1) (term (val e_2 ρ_1 μ_1)) 0)]
  [(val (|| e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) 0) (term (val e_2 ρ_1 μ_1)) 1)]
  [(val (== e_1 e_2) ρ_1 μ_1) ,(if (= (term (val e_1 ρ_1 μ_1)) (term (val e_2 ρ_1 μ_1))) 1 0)]
  [(val (chunk-read e_1 e_2) ρ_1 μ_1) (Chunk-read c_1 v_2)
                                      (where i_1 (val e_1 ρ_1 μ_1))
                                      (where v_2 (val e_2 ρ_1 μ_1))
                                      (side-condition (number? (term v_2)))
                                      (where ((i_b c_b) ... (i_1 c_1) (i_a c_a) ...) μ_1)])

; Metafunctions for control flow
; ------------------------------

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

; The abstract machine
; --------------------

;(define ⟶
;  (reduction-relation
;   ippc-machine #:domain m
;
;   (--> ((ρ_11 ... (x_a v_a0) ρ_12 ...) (((:= x_a e_a) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        ((ρ_11 ... (x_a v_a) ρ_12 ...) ((s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (where v_a (val e_a (ρ_11 ... (x_a v_a0) ρ_12 ...) ρ_2 μ_1))
;        "assignment")
;
;   (--> (ρ_1 (((label l_1 s_0) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (ρ_1 ((s_0 s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        "label")
;
;   (--> (ρ_1 (((if-goto e_1 l_1) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (ρ_1 ((s_t ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (side-condition (eq? (term (val e_1 ρ_1 ρ_2 μ_1)) 1))
;        (where (s_t ...) (goto l_1 (get-function-body x_f p_1)))
;        "if-goto-true")
;
;   (--> (ρ_1 (((if-goto e_1 l_1) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (ρ_1 ((s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (side-condition (eq? (term (val e_1 ρ_1 ρ_2 μ_1)) 0))
;        "if-goto-false")
;
;   (--> (ρ_1 (((:= x_a l_ret e_g e_args ...) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (ρ_1 ((s_g ...) x_g κ_g ρ_g μ_1 p_1))
;        (where x_g (val e_g ρ_1 ρ_2 μ_1))
;        (where (v_args ...) ((val e_args ρ_1 ρ_2 μ_1) ...))
;        (where (T_g x_g0 ((T_g2 x_g2) ...) ((T_g3 x_g3) ...) (s_g ...)) (get-function x_g p_1))
;        (where ρ_g ((x_g2 v_args) ... (x_g3 (garbage)) ...))
;        (where κ_g (l_ret (s_1 ...) x_g ρ_2 κ_1))
;        "call")
;
;   (--> (ρ_1 (((return e_1) s_1 ...) x_g (l_ret (s_f ...) x_f ρ_f κ_1) ρ_2 μ_1 p_1))
;        (ρ_1 ((s_ret ...) x_f (l_ret (s_f ...) x_f ρ_f2 κ_1) ρ_2 μ_1 p_1))
;        (where v_1 (val e_1 ρ_1 ρ_2 μ_1))
;        (where (((:= x_a l_ret0 e_g0 e_args0 ...)) s_ret ...) (goto l_ret (get-function-body x_f p_1)))
;        (where ((x_f1 v_a1) ... (x_a v_a0) (x_f2 v_a2) ...) ρ_f)
;        (where ρ_f2 ((x_f1 v_a1) ... (x_a v_1) (x_f2 v_a2) ...))
;        "return")
;
;   (--> ((ρ_11 ...) (((:= x_a (chunk-new e_1 e_2)) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        ((ρ_11 ... (x_a i_1)) ((s_1 ...) x_f κ_1 ρ_2 μ_2 p_1))
;        (where i_1 ,(gensym 'i))
;        (where v_1 (val e_1 ρ_1 ρ_2 μ_1))
;        (where v_2 (val e_2 ρ_1 ρ_2 μ_1))
;        (where ((i_b c_b) ...) μ_1)
;        (where μ_2 ((i_b c_b) ... (i_1 v_2)))
;        "chunk-new")
;
;   (--> (ρ_1 (((chunk-write e_1 e_2 e_3) s_1 ...) x_f κ_1 ρ_2 μ_1 p_1))
;        (ρ_1 ((s_1 ...) x_f κ_1 ρ_2 μ_2 p_1))
;        (where i_1 (val e_1 ρ_1 ρ_2 μ_1))
;        (where v_2 (val e_2 ρ_1 ρ_2 μ_1))
;        (side-condition (number? (term v_2)))
;        (where v_3 (val e_3 ρ_1 ρ_2 μ_1))
;        (where ((i_b c_b) ... (v_1 c_t) (i_a c_a) ...) μ_1)
;        (where c_t2 ,(list-set (term c_t) (term i_1) (term v_3)))
;        (where μ_2 ((i_b c_b) ... (v_1 c_t2) (i_a c_a) ...))
;        "chunk-write")
;        
;   ))
   
; (redex-match? ippc d (term (int foo ((int z)) ((int yy)) (:= yy bar (+ z 2)))))
; http://siek.blogspot.fr/2012/07/the-semantics-of-familiar-language.html
