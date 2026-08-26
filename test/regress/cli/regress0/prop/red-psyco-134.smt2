; COMMAND-LINE: --sat-solver=cadical
; DISABLE-TESTER: proof
; EXPECT: sat
(set-logic LIA)
(declare-const x Bool)
(declare-const x1 Bool)
(declare-fun R () Bool)
(assert (and (or R x1) (forall ((V Int)) (or (not R) (and x1 (or (not R) (= 1 V))) (and x1 x (or (not R) (= 1 V)))))))
(check-sat)
