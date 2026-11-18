; EXPECT: unsat
; Rewrite::IDOF_STRIP_SYM_LEN must have a complete proof, via RARE rule str-indexof-prefix-concat.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.indexof (str.++ s "a" t) (str.++ s "a") 0) 0))
(check-sat)
