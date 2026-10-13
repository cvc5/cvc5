; EXPECT: unsat
; Rewrite::RPL_CCTN_RPL must have a complete proof, via RARE rule str-replace-prefix-concat.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.replace (str.++ s "a" t) (str.++ s "a") u) (str.++ u t)))
(check-sat)
