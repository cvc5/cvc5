; COMMAND-LINE: --incremental -q --check-unsat-cores
; COMMAND-LINE: --incremental -q --check-unsat-cores --unsat-cores-mode=sat-proof
; EXPECT: sat
; EXPECT: sat
(declare-const i2 Int)
(declare-const i5 Int)
(declare-fun st2 () (Set Int))
(declare-fun st4 () (Set Int))
(declare-fun st9 () (Set Int))
(declare-const v6 Bool)
(assert (! (forall ((q12 Int) (q13 Bool)) (xor false true true false true true v6 (<= 5 i5 93 417 i2) true (subset st2 st4) true)) :named IP_4))
(declare-const i11 Int)
(assert (< (card st9) i11))
(assert (! (not (<= 5 i5 93 417 i2)) :named IP_46))
(check-sat)
(check-sat-assuming ((! (or v6 v6 v6) :named IP_12) (! (or false v6 v6) :named IP_56)))