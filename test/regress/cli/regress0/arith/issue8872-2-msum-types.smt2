; COMMAND-LINE: --ext-rew-prep=agg
; EXPECT: sat
(set-logic ALL)
(declare-fun v () Bool)
(declare-fun a () Real)
(declare-fun va () Real)
(assert (= (- a va) (ite v 0 1)))
(check-sat)
