; REQUIRES: unrestricted-mode
; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
; The equality between datatype terms forces U to be a singleton, so U is not
; monotonic even though no variable occurs directly in an equality.
(set-logic UFDT)
(declare-sort U 0)
(declare-datatype Box ((box (sel U))))
(declare-fun f (U) U)
(declare-fun c () U)
(declare-fun t () Box)
(assert (forall ((X U)) (= (box X) t)))
(assert (forall ((X U)) (not (= (f X) c))))
(check-sat)
