; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const x1 Bool)
(declare-const x4 Bool)
(declare-const x41 Bool)
(declare-const o Float32)
(assert (forall ((V Float32)) (fp.eq (ite x1 o (_ -oo 8 24)) (ite x4 (_ NaN 8 24) (ite x41 (_ NaN 8 24) (ite x V (_ NaN 8 24)))))))
(assert (exists ((V Float32)) (not (fp.eq (ite x4 (_ NaN 8 24) (ite x41 (_ NaN 8 24) (ite x V (_ NaN 8 24)))) (ite x1 o (_ -oo 8 24))))))
(check-sat)
