; --debug-check-models prints a diagnostic about an internal sygus-inst DT_SYGUS_BOUND fact; --check-models succeeds.
; DISABLE-TESTER: model
; EXPECT: sat
(set-logic NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((c Bool)) (> (div 1 0 (+ 1 (ite c a b))) 1)))
(check-sat)
