; COMMAND-LINE: --full-saturate-quant --no-ho-matching --ho-elim-store-ax
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-sort tptp.a 0)
(declare-fun tptp.cK ((-> tptp.a Bool) tptp.a) Bool)
(assert (not (=> (forall ((X (-> tptp.a Bool)) (Y (-> tptp.a Bool))) (=> (forall ((Xx tptp.a)) (=> (@ X Xx) (@ Y Xx))) (forall ((Xx tptp.a)) (=> (@ (@ tptp.cK X) Xx) (@ (@ tptp.cK Y) Xx))))) (forall ((Xx tptp.a)) (=> (forall ((S (-> tptp.a Bool))) (=> (forall ((Xx0 tptp.a)) (=> (@ (@ tptp.cK S) Xx0) (@ S Xx0))) (@ S Xx))) (@ (@ tptp.cK (lambda ((Xx0 tptp.a)) (forall ((S (-> tptp.a Bool))) (=> (forall ((Xx1 tptp.a)) (=> (@ (@ tptp.cK S) Xx1) (@ S Xx1))) (@ S Xx0))))) Xx))))))
(set-info :filename SEV310^5)
(check-sat-assuming ( true ))
