; COMMAND-LINE: --bv-solver=bitblast-internal --decision=justification --sat-solver=cadical
; EXPECT: sat
; REQUIRES: no-safe-mode
; The bit-blasting lemmas of the internal bit-blaster contain ITE-heavy
; circuits, for which the justification heuristic may find an assertion to be
; false in the current assignment without the SAT solver being in conflict
; (vivification in CaDiCaL may delete the redundant clauses of the Tseitin
; encoding of ITE).
(set-logic BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (forall ((x (_ BitVec 8))) (not (= (bvurem a x) b))))
(check-sat)
