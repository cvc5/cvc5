; cvc4 --lang smt

; This problem returns "unsat", but it is in fact "sat", by interpreting "a" with a domain of
; cardinality 1. The issue arises irrespective of the "--finite-model-find" option.

(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)
(declare-sort a 0)
(declare-datatypes () ((w (Wrap (unw a)))))
(declare-fun x () w)
(assert (forall ((y w)) (= x y)))
(check-sat)
