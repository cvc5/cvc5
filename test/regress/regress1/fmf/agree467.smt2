; COMMAND-LINE: --finite-model-find --lang=smt2.5
; EXPECT: unsat
; Preamble  --------------
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-datatypes () ((UNIT (Unit))))
(declare-datatypes () ((BOOL (Truth) (Falsity))))

; Decls     --------------
(declare-sort node$type 0)
(declare-sort value$type 0)
(define-sort Nodes$elem$type () node$type)
(declare-sort Nodes$t$type 0)
(declare-fun Nodes$empty () Nodes$t$type)
(declare-fun Nodes$mem (Nodes$elem$type Nodes$t$type) BOOL)
(declare-fun Nodes$add (Nodes$elem$type Nodes$t$type) Nodes$t$type)
(declare-fun Nodes$remove (Nodes$elem$type Nodes$t$type) Nodes$t$type)
(declare-fun Nodes$cardinality (Nodes$t$type) Int)
(declare-fun Nodes$union (Nodes$t$type Nodes$t$type) Nodes$t$type)
(declare-fun Nodes$disjoint (Nodes$t$type Nodes$t$type) BOOL)
;Nodes$disjoint_empty :
(assert (forall ((a Nodes$t$type)) (= (Nodes$disjoint a Nodes$empty) Truth)))
;Nodes$disjoint_comm :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (= (Nodes$disjoint a b) 
                                                    (Nodes$disjoint b a))))
;Nodes$mem_empty :
(assert (forall ((e Nodes$elem$type)) (not (= (Nodes$mem e Nodes$empty) 
                                           Truth))))
;Nodes$mem_add :
(assert (forall ((x Nodes$elem$type) (y Nodes$elem$type) (s Nodes$t$type)) 
        (= (Nodes$mem x (Nodes$add y s)) (ite (or (= x y) (= (Nodes$mem x s) 
                                                          Truth)) Truth 
                                         Falsity))))
;Nodes$mem_remove :
(assert (forall ((x Nodes$elem$type) (y Nodes$elem$type) (s Nodes$t$type)) 
        (= (Nodes$mem x (Nodes$remove y s)) (ite (and (not (= x y)) (= 
                                                                    (Nodes$mem 
                                                                    x s) 
                                                                    Truth)) 
                                            Truth Falsity))))
;Nodes$mem_union1 :
(assert (forall ((x Nodes$elem$type) (a Nodes$t$type)) (=> (= (Nodes$mem x a) 
                                                           Truth) (forall 
                                                                  ((b Nodes$t$type)) 
                                                                  (= 
                                                                  (Nodes$mem 
                                                                  x (Nodes$union 
                                                                    a b)) 
                                                                  Truth)))))
;Nodes$mem_union2 :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (= (Nodes$union a b) 
                                                    (Nodes$union b a))))
;Nodes$mem_union3 :
(assert (forall ((x Nodes$elem$type) (a Nodes$t$type) (b Nodes$t$type)) 
        (=> (= (Nodes$mem x (Nodes$union a b)) Truth) (or (= (Nodes$mem x a) 
                                                          Truth) (= (Nodes$mem 
                                                                    x b) 
                                                                 Truth)))))
;Nodes$mem_union4 :
(assert (forall ((a Nodes$t$type)) (= (Nodes$union a a) a)))
;Nodes$mem_union5 :
(assert (forall ((a Nodes$t$type)) (= (Nodes$union a Nodes$empty) a)))
;Nodes$empty_union :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (=> (= (Nodes$union a b) 
                                                        Nodes$empty) 
                                                    (= a Nodes$empty))))
;Nodes$card_empty :
(assert (= (Nodes$cardinality Nodes$empty) 0))
;Nodes$card_zero :
(assert (forall ((s Nodes$t$type)) (=> (= (Nodes$cardinality s) 0) (= 
                                                                   s 
                                                                   Nodes$empty))))
;Nodes$card_non_negative :
(assert (forall ((s Nodes$t$type)) (>= (Nodes$cardinality s) 0)))
;Nodes$card_add :
(assert (forall ((x Nodes$elem$type) (s Nodes$t$type)) (= (Nodes$cardinality 
                                                          (Nodes$add x s)) 
                                                       (ite (= (Nodes$mem 
                                                               x s) Truth) 
                                                       (Nodes$cardinality 
                                                       s) (+ (Nodes$cardinality 
                                                             s) 1)))))
;Nodes$card_remove :
(assert (forall ((x Nodes$elem$type) (s Nodes$t$type)) (= (Nodes$cardinality 
                                                          (Nodes$remove x s)) 
                                                       (ite (= (Nodes$mem 
                                                               x s) Truth) (- 
                                                       (Nodes$cardinality 
                                                       s) 1) (Nodes$cardinality 
                                                             s)))))
;Nodes$card_union :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (=> (= (Nodes$disjoint 
                                                           a b) Truth) 
                                                    (= (Nodes$cardinality 
                                                       (Nodes$union a b)) (+ 
                                                    (Nodes$cardinality 
                                                    a) (Nodes$cardinality b))))))
(declare-fun Nodes$eq (Nodes$t$type Nodes$t$type) BOOL)
;Nodes$eq_is_equality :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (= (Nodes$eq a b) 
                                                    (ite (= a b) Truth 
                                                    Falsity))))
;Nodes$equal1 :
(assert (forall ((a Nodes$t$type) (b Nodes$t$type)) (=> (forall ((x Nodes$elem$type)) 
                                                        (= (Nodes$mem x a) 
                                                        (Nodes$mem x b))) 
                                                    (= (Nodes$eq a b) 
                                                    Truth))))
(define-sort Values$elem$type () value$type)
(declare-sort Values$t$type 0)
(declare-fun Values$empty () Values$t$type)
(declare-fun Values$mem (Values$elem$type Values$t$type) BOOL)
(declare-fun Values$add (Values$elem$type Values$t$type) Values$t$type)
(declare-fun Values$remove (Values$elem$type Values$t$type) Values$t$type)
(declare-fun Values$cardinality (Values$t$type) Int)
(declare-fun Values$union (Values$t$type Values$t$type) Values$t$type)
(declare-fun Values$disjoint (Values$t$type Values$t$type) BOOL)
;Values$disjoint_empty :
(assert (forall ((a Values$t$type)) (= (Values$disjoint a Values$empty) 
                                    Truth)))
;Values$disjoint_comm :
(assert (forall ((a Values$t$type) (b Values$t$type)) (= (Values$disjoint 
                                                         a b) (Values$disjoint 
                                                              b a))))
;Values$mem_empty :
(assert (forall ((e Values$elem$type)) (not (= (Values$mem e Values$empty) 
                                            Truth))))
;Values$mem_add :
(assert (forall ((x Values$elem$type) (y Values$elem$type) (s Values$t$type)) 
        (= (Values$mem x (Values$add y s)) (ite (or (= x y) (= (Values$mem 
                                                               x s) Truth)) 
                                           Truth Falsity))))
;Values$mem_remove :
(assert (forall ((x Values$elem$type) (y Values$elem$type) (s Values$t$type)) 
        (= (Values$mem x (Values$remove y s)) (ite (and (not (= x y)) 
                                                   (= (Values$mem x s) 
                                                   Truth)) Truth Falsity))))
;Values$mem_union1 :
(assert (forall ((x Values$elem$type) (a Values$t$type)) (=> (= (Values$mem 
                                                                x a) 
                                                             Truth) (forall 
                                                                    (
                                                                    (b Values$t$type)) 
                                                                    (= 
                                                                    (Values$mem 
                                                                    x 
                                                                    (Values$union 
                                                                    a b)) 
                                                                    Truth)))))
;Values$mem_union2 :
(assert (forall ((a Values$t$type) (b Values$t$type)) (= (Values$union a b) 
                                                      (Values$union b a))))
;Values$mem_union3 :
(assert (forall ((x Values$elem$type) (a Values$t$type) (b Values$t$type)) 
        (=> (= (Values$mem x (Values$union a b)) Truth) (or (= (Values$mem 
                                                               x a) Truth) 
                                                        (= (Values$mem x b) 
                                                        Truth)))))
;Values$mem_union4 :
(assert (forall ((a Values$t$type)) (= (Values$union a a) a)))
;Values$mem_union5 :
(assert (forall ((a Values$t$type)) (= (Values$union a Values$empty) a)))
;Values$empty_union :
(assert (forall ((a Values$t$type) (b Values$t$type)) (=> (= (Values$union 
                                                             a b) Values$empty) 
                                                      (= a Values$empty))))
;Values$card_empty :
(assert (= (Values$cardinality Values$empty) 0))
;Values$card_zero :
(assert (forall ((s Values$t$type)) (=> (= (Values$cardinality s) 0) 
                                    (= s Values$empty))))
;Values$card_non_negative :
(assert (forall ((s Values$t$type)) (>= (Values$cardinality s) 0)))
;Values$card_add :
(assert (forall ((x Values$elem$type) (s Values$t$type)) (= (Values$cardinality 
                                                            (Values$add x s)) 
                                                         (ite (= (Values$mem 
                                                                 x s) 
                                                              Truth) 
                                                         (Values$cardinality 
                                                         s) (+ (Values$cardinality 
                                                               s) 1)))))
;Values$card_remove :
(assert (forall ((x Values$elem$type) (s Values$t$type)) (= (Values$cardinality 
                                                            (Values$remove 
                                                            x s)) (ite 
                                                                  (= 
                                                                  (Values$mem 
                                                                  x s) 
                                                                  Truth) (- 
                                                                  (Values$cardinality 
                                                                  s) 
                                                                  1) 
                                                                  (Values$cardinality 
                                                                  s)))))
;Values$card_union :
(assert (forall ((a Values$t$type) (b Values$t$type)) (=> (= (Values$disjoint 
                                                             a b) Truth) 
                                                      (= (Values$cardinality 
                                                         (Values$union a b)) (+ 
                                                      (Values$cardinality 
                                                      a) (Values$cardinality 
                                                         b))))))
(declare-fun Values$eq (Values$t$type Values$t$type) BOOL)
;Values$eq_is_equality :
(assert (forall ((a Values$t$type) (b Values$t$type)) (= (Values$eq a b) 
                                                      (ite (= a b) Truth 
                                                      Falsity))))
;Values$equal1 :
(assert (forall ((a Values$t$type) (b Values$t$type)) (=> (forall ((x Values$elem$type)) 
                                                          (= (Values$mem x a) 
                                                          (Values$mem 
                                                          x b))) (= (Values$eq 
                                                                    a b) 
                                                                 Truth))))
(define-sort node_set$type () (Array node$type BOOL))
(declare-fun mk_array_1 () (Array node$type BOOL))
;mk_array_1_def :
(assert (forall ((mk_array_1_index node$type)) (= (select mk_array_1 
                                                  mk_array_1_index) Falsity)))
(define-fun empty_node_set () node_set$type mk_array_1)
(define-sort node_pair_set$type () (Array node$type (Array node$type BOOL)))
(declare-fun mk_array_2 () (Array node$type BOOL))
;mk_array_2_def :
(assert (forall ((mk_array_2_index node$type)) (= (select mk_array_2 
                                                  mk_array_2_index) Falsity)))
(declare-fun mk_array_3 () (Array node$type (Array node$type BOOL)))
;mk_array_3_def :
(assert (forall ((mk_array_3_index node$type)) (= (select mk_array_3 
                                                  mk_array_3_index) mk_array_2)))
(define-fun empty_node_pair_set () node_pair_set$type mk_array_3)
(declare-fun mk_array_4 () (Array node$type BOOL))
;mk_array_4_def :
(assert (forall ((mk_array_4_index node$type)) (= (select mk_array_4 
                                                  mk_array_4_index) Truth)))
(declare-fun mk_array_5 () (Array node$type (Array node$type BOOL)))
;mk_array_5_def :
(assert (forall ((mk_array_5_index node$type)) (= (select mk_array_5 
                                                  mk_array_5_index) mk_array_4)))
(define-fun full_node_pair_set () node_pair_set$type mk_array_5)
(declare-fun input () (Array node$type value$type))
(declare-fun t () Int)
;positive_bound :
(assert (> t 0))
(define-sort message$type () Values$t$type)
(define-sort message_set$type () (Array node$type message$type))
(define-sort state$type () Values$t$type)
(define-sort state_set$type () (Array node$type state$type))
(define-fun null_message () message$type Values$empty)
(declare-fun mk_array_6 () (Array node$type message$type))
;mk_array_6_def :
(assert (forall ((mk_array_6_index node$type)) (= (select mk_array_6 
                                                  mk_array_6_index) null_message)))
(define-fun null_message_set () message_set$type mk_array_6)
(define-fun null_state () state$type Values$empty)
(declare-fun mk_array_7 () (Array node$type state$type))
;mk_array_7_def :
(assert (forall ((mk_array_7_index node$type)) (= (select mk_array_7 
                                                  mk_array_7_index) null_state)))
(define-fun null_state_set () state_set$type mk_array_7)
(declare-fun choose (Values$t$type) value$type)
;choosen_value :
(assert (forall ((vals Values$t$type)) (or (= vals Values$empty) (= (Values$mem 
                                                                    (choose 
                                                                    vals) 
                                                                    vals) 
                                                                 Truth))))
(define-sort failure_pattern$type () node_pair_set$type)
(define-fun is_faulty ((p node$type) (deliver failure_pattern$type)) BOOL 
(ite (exists ((q node$type)) (not (= (select (select deliver p) q) Truth))) 
Truth Falsity))
(define-fun is_silent ((p node$type) (deliver failure_pattern$type)) BOOL 
(ite (forall ((q node$type)) (not (= (select (select deliver p) q) Truth))) 
Truth Falsity))
(declare-datatypes () ((phase_state$type (init_phase) (send_phase) (recv_phase) (comp_phase))))
(declare-datatypes () ((clean_state$type (before) (active) (after))))

; Var Decls --------------
(declare-fun init_done () node_set$type)
(declare-fun crashed () Nodes$t$type)
(declare-fun comp_done () node_set$type)
(declare-fun chosen () (Array node$type BOOL))
(declare-fun recv_done () node_pair_set$type)
(declare-fun phase () phase_state$type)
(declare-fun clean () clean_state$type)
(declare-fun global_state () state_set$type)
(declare-fun messages () (Array node$type message_set$type))
(declare-fun deliver_message () failure_pattern$type)
(declare-fun crashing () Nodes$t$type)
(declare-fun round () Int)
(declare-fun send_done () node_pair_set$type)

; Asserts   --------------
(declare-fun mk_array_8 () (Array node$type BOOL))
;mk_array_8_def :
(assert (forall ((mk_array_8_index node$type)) (= (select mk_array_8 
                                                  mk_array_8_index) Falsity)))
(declare-fun mk_array_9 () (Array node$type message_set$type))
;mk_array_9_def :
(assert (forall ((mk_array_9_index node$type)) (= (select mk_array_9 
                                                  mk_array_9_index) null_message_set)))
(assert (not (=> (and (and (and (and (and (and (and (and (and (and (and 
                                                                   (and 
                                                                   (= 
                                                                   clean 
                                                                   before) 
                                                                   (= 
                                                                   global_state 
                                                                   null_state_set)) 
                                                                   (= 
                                                                   messages 
                                                                   mk_array_9)) 
                                                              (= deliver_message 
                                                              full_node_pair_set)) 
                                                         (= comp_done 
                                                         empty_node_set)) 
                                                    (= recv_done empty_node_pair_set)) 
                                               (= send_done empty_node_pair_set)) 
                                          (= init_done empty_node_set)) 
                                     (= phase init_phase)) (= crashing 
                                                           Nodes$empty)) 
                           (= crashed Nodes$empty)) (= round 0)) (= chosen 
                                                                 mk_array_8)) 
             (forall ((n node$type)) (=> (and (= (select chosen n) Truth) 
                                         (= round (+ t 1))) (and (forall 
                                                                 ((n node$type) (m node$type)) 
                                                                 (= (select 
                                                                    (select 
                                                                    send_done 
                                                                    n) 
                                                                    m) 
                                                                 Truth)) 
                                                            (forall (
                                                                    (n node$type) (m node$type)) 
                                                            (= (select 
                                                               (select 
                                                               recv_done 
                                                               n) m) 
                                                            Truth))))))))

(check-sat)
