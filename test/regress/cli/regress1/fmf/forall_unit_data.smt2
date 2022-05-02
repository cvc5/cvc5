; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-option :produce-models true)
(set-option :produce-assertions true)
(set-logic ALL)
(declare-sort a 0)
(declare-datatypes ((w 0)) (((Wrap (unw a)))))
(declare-fun x () w)
(assert (forall ((y w)) (= x y)))
(check-sat)
