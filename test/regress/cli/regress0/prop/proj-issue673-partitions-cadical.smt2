; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :sat-solver cadical)
(set-option :compute-partitions 3)
(set-option :produce-unsat-assumptions true)
(define-fun f () Bool false)
(check-sat)
