; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(set-option :check-unsat-cores true)
(set-option :incremental true)
(set-option :produce-proofs true)
(declare-const x1 Bool)
(declare-const x5 Bool)
(declare-const x6 Bool)
(declare-const x Bool)
(assert (distinct (or (distinct (distinct true x) (= (distinct true x) (and (distinct true x) (distinct x6 x1)))) (xor x6 x1)) (distinct x1 (= (distinct x1 x5) (not (= (distinct true x) (ite x1 true x)))))))
(assert (distinct x1 (= (distinct x1 x5) (not (= (distinct true x) (ite x1 true x))))))
(check-sat-assuming (true))
(check-sat)
