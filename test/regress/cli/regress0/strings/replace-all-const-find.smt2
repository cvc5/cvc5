; EXPECT: unsat
; Rewrite::REPLALL_CONST must have a complete proof, via RARE rule str-replace-all-find.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.replace_all "ab" "b" u) (str.++ "a" u)))
(check-sat)
