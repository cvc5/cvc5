; REQUIRES: unrestricted-mode
; COMMAND-LINE: --arrays-exp
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((Option 1)) ((par (X) ((none) (some (val X))))))
(declare-datatype R ((mk (o (Option Bool)))))
; R has 3 values, all of which are stored to 1
(assert (not (= (store (store (store ((as const (Array R Int)) 0) (mk (as none (Option Bool))) 1) (mk (some true)) 1) (mk (some false)) 1) ((as const (Array R Int)) 1))))
(check-sat)
