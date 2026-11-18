; EXPECT: unsat
; Rewrite::UPD_OOB must have a complete proof, via RARE rule str-update-oob.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update s (str.len s) u) s))
(check-sat)
