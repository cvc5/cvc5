; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-unsat-cores true)
(set-option :produce-abducts true)
(declare-const y (_ BitVec 2))
(get-abduct abd (= y #b00))
