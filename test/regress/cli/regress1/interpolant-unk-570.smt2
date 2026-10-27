; COMMAND-LINE: -q
; EXPECT: fail
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-fun x () (Set Int))
(get-interpolant A (set.is_singleton (set.minus x x)))
