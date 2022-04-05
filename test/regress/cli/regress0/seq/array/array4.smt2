; COMMAND-LINE: --incremental --strings-exp --seq-array=eager
; EXPECT: unsat

(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)

(declare-sort Element 0)
(declare-fun a1 () (Seq Element))
(declare-fun a2 () (Seq Element))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (let ((?v_0 (seq.update a2 i1 (seq.unit (seq.nth a1 i1))))
              (?v_1 (seq.update a1 i1 (seq.unit (seq.nth a2 i1)))))
             (= (seq.update ?v_1 i2 (seq.unit (seq.nth ?v_0 i2))) 
                (seq.update ?v_0 i2 (seq.unit (seq.nth ?v_1 i2))))))
(assert (not (= a1 a2)))
(check-sat)
(exit)
