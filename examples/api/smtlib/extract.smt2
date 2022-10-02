(set-logic QF_BV)

(declare-const a (_ BitVec 32))

(define-const a_31_1 (_ BitVec 31) ((_ extract 31 1) a))
(define-const a_30_0 (_ BitVec 31) ((_ extract 30 0) a))
(define-const a_31_31 (_ BitVec 1) ((_ extract 31 31) a))
(define-const a_0_0 (_ BitVec 1) ((_ extract 0 0) a))

(echo "Asserting a_31_1 = a_30_0")
(assert (= a_31_1 a_30_0))

(echo "Check unsatisfiability assuming a_31_31 != a_0_0")
(check-sat-assuming ((not (= a_31_31 a_0_0))))
