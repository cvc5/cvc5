; COMMAND-LINE: --unconstrained-simp
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (distinct a c))
(assert (= a b (= b c)))
(set-info :status sat)
(check-sat)
