(set-logic ALL)
(declare-fun v () (Seq (Seq Int)))
(declare-fun a () (Seq Int))
(declare-fun r () (Seq Int))
(declare-fun r3 () (Seq (Seq Int)))

(assert (and
  (not (= v r3))
  (not (= v (seq.unit (as seq.empty (Seq Int)))))
  (not (= r3 (seq.unit (as seq.empty (Seq Int)))))))

(set-info :status sat)
(check-sat)
