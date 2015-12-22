; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)
(declare-sort a 0)
(declare-datatypes () ((w (Wrap (unw a)))))
(declare-fun x () w)
(assert (forall ((y w)) (= x y)))
(check-sat)
