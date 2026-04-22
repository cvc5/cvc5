; COMMAND-LINE: --mbqi-enum
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort u 0)
(declare-fun cP (u u) Bool)
(assert (not (=> (and (forall ((Xx u)) (@ (@ cP Xx) Xx)) (forall ((Xx u) (Xy u) (Xz u)) (let ((_let_1 (@ cP Xx))) (=> (and (@ _let_1 Xy) (@ (@ cP Xz) Xy)) (@ _let_1 Xz))))) (forall ((Xu u) (Xv u) (Xw u)) (let ((_let_1 (@ cP Xu))) (=> (and (@ _let_1 Xv) (@ (@ cP Xv) Xw)) (@ _let_1 Xw)))))))
(set-info :filename SYO102^5)
(check-sat-assuming ( true ))
