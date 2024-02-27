; COMMAND-LINE: --lemma-inprocess=full
; COMMAND-LINE: --lemma-inprocess=full --lemma-inprocess-subs=all --lemma-inprocess-infer-eq-lit
; COMMAND-LINE: --lemma-inprocess=light
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-sort s 0)
(declare-datatypes ((ms 0)) (((a))))
(declare-datatypes ((m 0)) (((c (ml ms)))))
(declare-fun sf () s)
(declare-fun h () (Array s m))
(assert (not (=> (and (forall ((n s)) (not (= a (ml (select h n)))))) (= a (ml (select h sf))) false)))
(check-sat)
