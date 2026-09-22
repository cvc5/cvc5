; REQUIRES: unrestricted-mode
; COMMAND-LINE: --no-cegqi --mbqi
; EXPECT: unsat
; REQUIRES: poly
; DISABLE-TESTER: cpc
; DISABLE-TESTER: lfsc
; MBQI instantiates with a real algebraic number here, which cannot be
; expressed in external proof formats (see wishue #143).
(set-logic NRA)
(set-info :status unsat)
(assert (forall ((x Real)) (or (< x 0.0) (not (= (* x x) 2.0)))))
(check-sat)
