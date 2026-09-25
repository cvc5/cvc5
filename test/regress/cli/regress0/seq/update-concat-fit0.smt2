; EXPECT: unsat
; Rewrite::UPD_EVAL_SYM must have a complete proof, via RARE rule str-update-concat-fit0.
(set-logic ALL)
(declare-const p (Seq String))
(declare-const x String)
(declare-const y String)
(assert (distinct (seq.update (seq.++ (seq.unit x) p) 0 (seq.unit y)) (seq.++ (seq.unit y) p)))
(check-sat)
