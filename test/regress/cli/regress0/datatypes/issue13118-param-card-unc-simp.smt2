; REQUIRES: unrestricted-mode
; COMMAND-LINE: --unconstrained-simp
; EXPECT: unsat
(set-logic QF_UFDTLIA)
(declare-datatypes ((Option 1)) ((par (X) ((none) (some (val X))))))
(declare-fun f ((Option (Option Bool))) Int)
(declare-const x (Option (Option Bool)))
; (Option (Option Bool)) has 4 values, all of which are mapped to 0
(assert (= (f (as none (Option (Option Bool)))) 0))
(assert (= (f (some (as none (Option Bool)))) 0))
(assert (= (f (some (some true))) 0))
(assert (= (f (some (some false))) 0))
(assert (= (f x) 1))
(check-sat)
