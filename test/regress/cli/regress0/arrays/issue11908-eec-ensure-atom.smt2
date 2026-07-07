; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
(set-logic ALIA)
(declare-const x (Array Int Int))
(declare-fun j () Int)
(assert (and (= 0 (select x (+ j 1))) (or (forall ((?V_25 Int)) (or (forall ((?V_26 Int)) (> 0 j))))) (exists ((?V_19 Int)) (and (exists ((?V_20 Int)) (= 1 (select x ?V_20)))))))
(check-sat)
