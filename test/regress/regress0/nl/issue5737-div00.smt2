; COMMAND-LINE: --ext-rew-prep -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (> (div 0 0) 0))
(check-sat)
