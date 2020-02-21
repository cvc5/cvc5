(set-info :smt-lib-version 2.5)
(set-logic QF_SLIA)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun z () String)

;big num test
(assert (= x (int.to.str 4785582390527685649)))
;should be ""
(assert (= y (int.to.str (- 9))))

;big num
(assert (= i (str.to.int "783914785582390527685649")))
;should be -1
(assert (= j (str.to.int "-783914785582390527685649")))

(check-sat)
