; REQUIRES: unrestricted-mode
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic ALL)
(set-option :proof-rewrite-rcons-rec-limit 14966763729191485587)
(set-option :check-proof-steps true)
(declare-const x Real)
(check-sat-assuming ((and (= x (/ 0.0 x)) (= 1.0 (/ 0.0 0.0)))))
