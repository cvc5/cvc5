; COMMAND-LINE: -q
; SCRUBBER: sed 's/(.*//g'
; EXPECT: sat
(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-models true)
(declare-const _x29 Real)
(check-sat)
(get-value ((forall ((_x56 Real)) (=> (>= _x29 _x56 _x29) (>= _x29 _x56 _x29)))))