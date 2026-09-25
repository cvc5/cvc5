; COMMAND-LINE: -i --sat-solver=cadical
; Proof checking fails after pop: the subsequent unsat proof contains
; a free assumption (ProofNodeManager::mkScope).
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun a () Real)
(assert (= 1.0 (/ 0.0 a)))
(set-info :status sat)
(check-sat)
(assert (= 0.0 (+ a 1.0)))
(set-info :status unsat)
(check-sat-assuming (true))
(set-info :status unsat)
(check-sat)
