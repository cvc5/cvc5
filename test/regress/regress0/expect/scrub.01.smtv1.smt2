; SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/'
; EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
; EXPECT: The fact in question: TERM
; EXPECT: ")
; EXIT: 1
(set-option :incremental false)
(set-info :status unknown)
(set-logic QF_LRA)
(declare-fun n () Real)
(assert (= (/ n n) 1))
(check-sat)
(exit)
