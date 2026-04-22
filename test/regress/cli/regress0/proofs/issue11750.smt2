; COMMAND-LINE: --proof-granularity=dsl-rewrite
; EXPECT: unsat
(set-logic UF)
(declare-sort I 0)
(declare-fun m (I I) Bool)
(declare-fun s (I) I)
(assert (forall ((smt__b I) (smt__f I)) (! (or (m smt__f (s smt__b)) (not (= smt__b (s smt__f)))) :pattern ((s smt__f)))))
(assert (forall ((smt__f I)) (= smt__f (s smt__f))))
(declare-fun sm () I)
(assert (not (m sm (s sm))))
(check-sat)
