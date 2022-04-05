; EXPECT: sat
(set-logic ALL)
(set-option :check-proofs true)
(declare-fun a () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (not a))
(assert (not (ite a d (not c))))
(check-sat)
