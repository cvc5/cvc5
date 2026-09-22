; COMMAND-LINE: --safe-mode=safe --check-proofs
; EXPECT: unsat
; Rewrite::UPD_EVAL_SYM must have a complete proof, via RARE rule str-update-fit.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update (str.substr s 0 1) 0 (str.substr s 0 1)) (str.substr s 0 1)))
(check-sat)
