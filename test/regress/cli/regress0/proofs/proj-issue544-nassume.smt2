; EXPECT: sat
(set-logic ALL)
(set-option :produce-unsat-assumptions true)
(set-option :incremental true)
(set-option :proof-mode sat-proof)
(declare-fun x (Bool) Bool)
(assert (distinct false (x (not (x (x false))))))
(check-sat-assuming (true))
