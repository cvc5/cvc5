; COMMAND-LINE: --produce-abducts --sygus-core-connective
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-const x Bool)
(declare-fun b () Bool)
(assert (= b x))
(check-sat)
