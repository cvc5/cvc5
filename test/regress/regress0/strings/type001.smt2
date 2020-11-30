(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun z () String)

;big num test
(assert (= x (str.from_int 4785582390527685649)))
;should be ""
(assert (= y (str.from_int (- 9))))

;big num
(assert (= i (str.to_int "783914785582390527685649")))
;should be -1
(assert (= j (str.to_int "-783914785582390527685649")))

(check-sat)
