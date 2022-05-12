; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((dA 0)) (((A))))
(declare-datatypes ((Loc 0)) (((G (g dA) (ag Int)))))
(declare-sort v 0)
(declare-datatypes ((T 0) (U 0)) (((E) (I (ii Int)) (D (d Int)) (V (vv U))) ((R (rr v)))))
(declare-sort b 0)
(declare-sort l 0)
(declare-datatypes ((T@M 0)) (((M (dom b) (cnt l)))))
(declare-fun e () U)
(declare-fun m (T) v)
(declare-fun iseq (T T) Bool)
(declare-fun sel (v Int) T)
(declare-fun st (v) v)
(declare-fun s (l Loc) T)
(declare-fun sb (Loc) Bool)
(declare-fun m0 () T@M)
(declare-fun a () Bool)
(declare-fun im () Loc)
(declare-fun o (Loc T) l)
(declare-fun i () T)
(assert (forall ((?x0 v) (?x1 Int) (?x2 T)) (= ?x2 (sel (st ?x0) ?x1))))
(assert (forall ((v1 T) (v2 T)) (= (iseq v1 v2) (forall ((i Int)) (iseq (sel (rr (vv v1)) i) (sel (rr (vv v2)) i))))))
(assert (forall ((?x1 Loc) (?x2 T)) (= ?x2 (s (o ?x1 ?x2) ?x1))))
(assert (and 
(not a) 
(forall ((?a9 T)) (or (is-D ?a9) (sb (G A (d ?a9))))) 
(or 
(not (=> a (forall (($a T)) (sb (G A (d $a)))))) 
(and 
  (not (sb (G A (d i))))
  (= im (G A (d (I 0)))) 
  (= m0 (M (dom m0) (o im (V (R (st (m E))))))) 
  (iseq (s (cnt m0) (G A (d i))) (V (R (rr e)))) 
  (or 
    (exists ((?a1 T)) (not (iseq (sel (rr (vv (s (cnt m0) (G A (d ?a1))))) 0) (sel (rr (vv (s (cnt m0) (G A (d ?a1))))) 0)))) 
    (forall ((?a3 T)) (sb (G A (d ?a3)))))))))
(check-sat)
