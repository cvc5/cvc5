; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () Bool)
(assert (forall ((b Bool)) (not (xor b (=> (and (not (not (and (not (or (not
(xor a (exists ((b Bool)) true))) (and (not (not (xor a (xor (not (xor a
(exists ((b Bool)) true) )) true))))))) b))) (not b)) true)))))
(check-sat)
