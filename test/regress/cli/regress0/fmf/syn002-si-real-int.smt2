; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort $$unsorted 0)
(declare-fun $$rtu (Real) $$unsorted)
(declare-fun $$utr ($$unsorted) Real)
(declare-fun p ($$unsorted) Bool)
(assert (and (= ($$utr ($$rtu 12.0)) 12.0) (= ($$utr ($$rtu (/ 41 152))) (/ 41 152)) ))
(assert (forall ((x $$unsorted)) (p x)))
(check-sat)
