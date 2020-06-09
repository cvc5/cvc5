; COMMAND-LINE: --fmf-fun -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun a (Int) Bool)
(declare-fun b (Int) Bool)
(assert (= (a 0) (b 0)))
(push)
(check-sat)
(pop)
(check-sat)
