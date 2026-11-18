; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :check-proof-steps true)
(assert (ite (bvuge (_ bv0 74) (bvsdiv ((_ zero_extend 73) __) (_ bv9444732965739290427392 74))) false true))
(check-sat)
