; COMMAND-LINE: --model-verify --produce-models
; EXPECT: sat
(set-logic HO_ALL)
(set-option :sets-exp true)
(declare-const s (Set Int))
(assert (= (set.filter (lambda ((x Int)) (> x 0)) s) s))
(assert (set.member 5 s))
(assert (= (set.card s) 1))
(check-sat)
