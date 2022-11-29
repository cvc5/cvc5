; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic ALL)
(set-option :check-models true)
(set-option :incremental true)
(set-option :solve-bv-as-int sum)
(declare-fun uf6 (Bool) Bool)
(declare-fun uf7 (Bool) Bool)
(assert (uf7 true))
(push 1)
(assert (uf6 (uf7 true)))
(check-sat)
