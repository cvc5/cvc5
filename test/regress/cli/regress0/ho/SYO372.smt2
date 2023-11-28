; COMMAND-LINE: --mbqi
; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(declare-sort tptp.b 0)
(declare-sort tptp.gtype 0)
(declare-fun tptp.g (tptp.b) Bool)
(declare-fun tptp.h ((-> tptp.b Bool)) tptp.gtype)
(declare-fun tptp.f (tptp.b) Bool)
(assert (not (=> (forall ((Xx tptp.b)) (= (@ tptp.f Xx) (@ tptp.g Xx))) (= (@ tptp.h tptp.f) (@ tptp.h tptp.g)))))
(set-info :filename SYO372^5)
(check-sat-assuming ( true ))
