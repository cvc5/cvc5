; COMMAND-LINE: --produce-abducts --sygus-core-connective
; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(declare-fun b () Bool)
(assert (= b x))
(check-sat)
