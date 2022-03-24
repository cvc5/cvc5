; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :sygus-inference true)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (= (exp a) (exp b)))
(assert (< (exp b) (exp c)))
(check-sat)
