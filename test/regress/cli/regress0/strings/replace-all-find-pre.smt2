; COMMAND-LINE: --safe-mode=safe --check-proofs
; EXPECT: unsat
; Rewrite::REPLALL_CONST must have a complete proof, via RARE rule str-replace-all-find-pre.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.replace_all "ab" "a" u) (str.++ u "b")))
(check-sat)
