; EXPECT: unsat
; Rewrite::UPD_EVAL_SYM must have a complete proof, via RARE rule str-update-in-first-concat.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update (str.++ "a" s) 0 "a") (str.++ "a" s)))
(check-sat)
