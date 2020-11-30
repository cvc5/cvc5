; EXPECT: unsat
(set-logic AUFBV)
(set-info :status unsat)
(set-info :category "crafted")
(declare-sort Element 0)

(declare-fun a1 () (Array (_ BitVec 8) Element))
(declare-fun a2 () (Array (_ BitVec 8) Element))
(declare-fun a3 () (Array (_ BitVec 8) Element))
(declare-fun a4 () (Array (_ BitVec 8) Element))

(declare-fun i2 () (_ BitVec 8))
(declare-fun i3 () (_ BitVec 8))

(declare-fun e1 () Element)
(declare-fun e2 () Element)

(assert (not (= e1 e2)))
(assert (= a3 (store a1 (_ bv3 8) e1)))
(assert (= a4 (store a2 (_ bv3 8) e1)))
(assert (= (select a3 (_ bv2 8)) e1))
(assert (= (select a4 (_ bv2 8)) e2))

; (assert (eqrange a3 a4 (_ bv0 8) (_ bv2 8)))

(assert (forall ((x (_ BitVec 8)))
    (=> (and (bvule (_ bv0 8) x) (bvule x (_ bv2 8))) (= (select a3 x) (select a4 x)))
    ))


(check-sat)
(exit)
