; EXPECT: unsat
; Rewrite::UPD_EVAL_SYM must have a complete proof, via RARE rule str-update-concat-fit.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update (str.++ s "a") (str.len s) "a") (str.++ s "a")))
(check-sat)
