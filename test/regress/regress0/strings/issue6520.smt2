; COMMAND-LINE: --ext-rew-prep
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (= (str.++ "AB" b c) (str.++ c "B" a)))
(set-info :status sat)
(check-sat)
