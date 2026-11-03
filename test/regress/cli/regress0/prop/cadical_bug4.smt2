; COMMAND-LINE: -i --sat-solver=cadical
; Proof testing was disabled in #11272, before CaDiCaL supported proofs.
; TODO: Revalidate the inherited external proof checks before removing this.
; DISABLE-TESTER: proof
(set-logic QF_LIA)
(declare-fun s () Int)
(push)
(pop)
(assert (> 0 s))
(push)
(assert (= s 0))
(set-info :status unsat)
(check-sat)
(pop)
(push)
(push)
(pop)
