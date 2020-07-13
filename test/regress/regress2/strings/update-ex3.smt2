(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun s () String)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= s (str.update (str.update "ABCDEFG" x "ZZZ") y "X")))
(assert (not (str.contains s "B")))
(assert (not (str.contains s "D")))
(assert (not (str.contains s "G")))

(check-sat)
