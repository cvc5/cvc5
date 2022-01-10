; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-const x Real)
(set-option :sygus-core-connective true)
(check-sat-assuming ((= real.pi x)))
