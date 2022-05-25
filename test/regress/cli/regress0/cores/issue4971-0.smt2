; COMMAND-LINE: --incremental --cegqi-full --produce-unsat-cores
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: (
; EXPECT: IP_1
; EXPECT: )
(set-logic ALL)
(declare-const v1 Bool)
(declare-const v9 Bool)
(declare-const v14 Bool)
(declare-const i4 Int)
(declare-const v16 Bool)
(assert (! (forall ((q0 Bool) (q1 Bool) (q2 (_ BitVec 10)) (q3 Bool) (q4 (_ BitVec 10))) (=> (distinct (_ bv827 10) q2 q4) (xor q1 q0))) :named IP_1))
(declare-const v21 Bool)
(assert (! (or v9 v21 v16) :named IP_33))
(assert (! (or (< (abs 404) i4) v14 v1) :named IP_51))
(check-sat)
(check-sat-assuming (IP_33 IP_51))
(get-unsat-core)
