; COMMAND-LINE: --produce-interpolants --interpolants-mode=default --sygus-enum=fast --check-interpolants
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun y () (_ BitVec 4))
(assert (= (select a y) (_ bv0 4)))
(get-interpolant A (distinct (select a y) (_ bv1 4)))
