; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(set-option :fmf-bound true)
(declare-fun X () (Bag Int))
; the sum over the distinct elements of X and the sum over its occurrences can
; disagree on a threshold, e.g. for X = {60, 60}. This is the core of a query
; that neither the sets solver nor the default bags solver can answer.
(assert (not (=
  (>= (bag.fold (lambda ((x Int) (a Int)) (+ a x)) 0 (bag.setof X)) 100)
  (>= (bag.fold (lambda ((x Int) (a Int)) (+ a x)) 0 X) 100))))
(check-sat)
