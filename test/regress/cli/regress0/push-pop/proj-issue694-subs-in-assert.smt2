; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(set-option :repeat-simp true)
(declare-const x (Seq Bool))
(declare-const x1 (Seq Bool))
(assert (and (seq.contains seq.empty x) (not (seq.contains x x1))))
(check-sat)
(assert (seq.contains x x1))
(check-sat)
