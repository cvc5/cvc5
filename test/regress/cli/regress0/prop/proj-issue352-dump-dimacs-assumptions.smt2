; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(set-option :produce-unsat-assumptions true)
(set-option :minisat-dump-dimacs true)
(check-sat-assuming (x false))
