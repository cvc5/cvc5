; COMMAND-LINE: --safe-mode=safe --check-proofs
; EXPECT: unsat
; Rewrite::UPD_EMPTYSTR must have a complete proof, via RARE rule str-update-empty.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update "" n u) ""))
(check-sat)
