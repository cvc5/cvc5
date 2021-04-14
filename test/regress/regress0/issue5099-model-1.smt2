; COMMAND-LINE: -m
; EXPECT: sat
; EXPECT: ((baz true))
(set-logic QF_NIRA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (! (or (= a (div 0 b))) :named baz))
(assert (and (> b 5)))
(check-sat)
(get-assignment)
