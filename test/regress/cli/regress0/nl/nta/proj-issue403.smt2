; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :global-declarations true)
(declare-const _x1 Real)
(assert (let ((_let0 real.pi))(<= (/ _let0 _x1) _let0)))
(check-sat)
