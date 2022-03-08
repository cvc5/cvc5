; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :global-declarations true)
(set-option :sets-ext true)
(check-sat-assuming ( (let ((_let0 real.pi))(set.member (- _let0) (set.complement (set.singleton _let0))))))
