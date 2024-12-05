; REQUIRES: cocoa
(set-option :check-models true)
(set-logic QF_ALL)
(set-info :status sat)
(declare-const x0 (_ FiniteField 13))
(declare-const x3 Int)
(declare-const x7 (_ FiniteField 17))
(declare-fun x (Bool (_ FiniteField 17) Bool Int (_ FiniteField 13)) Bool)
(declare-fun x ((_ FiniteField 17) (Set (_ FiniteField 13)) (_ FiniteField 17) String (_ FiniteField 17)) (_ FiniteField 17))
(assert (x false (x x7 (set.singleton x0) #f88m17 (str.from_code x3) #f88m17) false 0 #f80m13))
(check-sat)

