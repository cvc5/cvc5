; COMMAND-LINE: --force-logic=UFLIRA
; SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/'
; EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
; EXPECT: The fact in question: TERM
; EXPECT: ")
; EXIT: 1
(declare-sort $$unsorted 0)
(assert (not (forall ((X Int)) (= (* X X) (to_real 1)))))
(set-info :filename scrub.09)
(check-sat-assuming ( true ))
