; EXPECT: unsat
; Rewrite::UPD_OOB must have a complete proof, via RARE rule str-update-oob.
(set-logic ALL)
(declare-const p (Seq String))
(declare-const q (Seq String))
(declare-const x String)
(assert (distinct (seq.update p (seq.len p) (seq.unit x)) p))
(check-sat)
