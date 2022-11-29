; EXPECT: sat
(set-logic ALL)
(set-option :fmf-bound true)
(declare-fun x (Bool Bool) Bool)
(assert (forall ((x4 Bool)) (x x4 (x false false))))
(check-sat)
