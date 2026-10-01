; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((T 0) (D 0))
  (((E) (I (t Int)) (z (v D)))
   ((z (v U)))))
(declare-datatypes ((H 0)) (((M (h T)))))
(declare-fun S (U Int) T)
(declare-fun n () H)
(assert
 (and
  (forall ((i Int))
    (or
     (forall ((z Int))
       (< (t (S (v (v (S (v (v (h n))) 1))) (t E)))
          (t (S (v (v (S (v (v (h n))) (str.len "3")))) (t E)))))))))
(check-sat)
