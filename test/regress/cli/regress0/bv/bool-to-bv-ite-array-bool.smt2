; COMMAND-LINE: --bool-to-bv=all --simplification=none
; EXPECT: sat
; checks that bool-to-bv pass handles arrays over booleans correctly
(set-logic QF_ABV)

(declare-const A (Array Bool Bool))
(declare-const B (Array Bool Bool))
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)

(assert (= A (store B b1 b2)))
(assert (= b3 (select A (select B b2))))
(assert (=> b1 b2))
(assert (not (and b2 (ite b3 b1 b2))))
(assert (=> b3 b1))
(assert (= b4 (select B b2)))
(assert (xor b4 b2))

(check-sat)