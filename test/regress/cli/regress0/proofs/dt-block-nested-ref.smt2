; EXPECT: unsat
;; The datatypes below are not mutually recursive, hence they must be printed in
;; separate blocks in proofs. Otherwise, R in (Tuple R) would be a nested
;; reference to a datatype of the same block, which Logos does not support.
(set-logic ALL)
(declare-datatypes ((R 0)) (((mk))))
(declare-datatypes ((D 0)) (((dc (x (Tuple R))))))
(declare-const d1 D)
(assert (not (= ((_ tuple.select 0) (x d1)) mk)))
(check-sat)
