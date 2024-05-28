; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :debug-check-models true)
(declare-sort _u0 0)
(declare-const _x13 _u0)
(declare-const _x24 _u0)
(assert (set.member (set.choose (set.insert _x24 (set.singleton _x13))) (set.singleton _x24)))
(check-sat)
