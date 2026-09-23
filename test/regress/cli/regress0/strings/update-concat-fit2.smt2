; EXPECT: unsat
; Rewrite::UPD_EVAL_SYM must have a complete proof, via RARE rule str-update-concat-fit2.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update (str.++ "a" s "b") (+ (str.len s) 1) "a") (str.++ "a" s "a")))
(check-sat)
