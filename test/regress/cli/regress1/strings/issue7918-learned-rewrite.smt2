; COMMAND-LINE: --learned-rewrite --no-produce-proofs
; EXPECT: sat
(set-logic ALL)
(declare-fun v () String)
(assert (= "" (str.substr v 0 1)))
(check-sat)
