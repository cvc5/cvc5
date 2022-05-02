; EXPECT: unknown
; EXPECT: (:reason-unknown incomplete)
(set-logic AUFLIA)
(set-info :source | 
  Boogie/Spec# benchmarks.
  This benchmark was translated by Michal Moskal.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun select2 (Int) Int)
(declare-fun store2 (Int) Int)
(assert (forall ((?A Int) (?o Int) (?f Int) (?p Int) (?g Int) (?v Int)) (=> (not (= ?o ?p)) (= (select2 (store2 ?A)) (select2 ?A)))))
(check-sat)
(get-info :reason-unknown)
(exit)
