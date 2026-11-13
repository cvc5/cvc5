; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --sat-solver=cadical --unsat-cores-mode=sat-proof
; EXPECT: unsat
; EXPECT: (
; EXPECT: A
; EXPECT: B
; EXPECT: )
; CaDiCaL refutes the assumptions of the two user levels directly from the
; unit clauses of A and B, without deriving a clause first; the unsat core
; must contain both assertions.
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun a () U)
(push 1)
(assert (! (p a) :named A))
(push 1)
(assert (! (not (p a)) :named B))
(check-sat)
(get-unsat-core)
