; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :check-proofs true)
(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert y)
(assert (not z))
(assert (ite x y z))
(check-sat)

(reset)

(set-logic ALL)
(set-option :check-proofs true)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert c)
(assert (not b))
(assert (ite a b c))
(check-sat)
