; COMMAND-LINE: --safe-mode=safe --check-proofs
; EXPECT: unsat
; Rewrite::IDOF_LEN must have a complete proof, via RARE rule str-indexof-len-oob2.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.indexof (str.rev s) (str.++ "a" s) n) (- 1)))
(check-sat)
