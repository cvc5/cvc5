; COMMAND-LINE: --force-logic=QF_LRA
; EXIT: 1
; EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
; EXPECT: The fact in question: TERM
; EXPECT: ")
;
;
; SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/' -e 's/in a linear logic: .*$/in a linear logic: TERM/' -e '/^[[:space:]]*$/d'
(set-logic ALL)
(set-option :incremental false)
(declare-fun n () Real)
(check-sat-assuming ( (= (/ n n) 1) ))
