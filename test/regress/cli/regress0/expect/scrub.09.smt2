; COMMAND-LINE: --force-logic=UFLIRA
; EXPECT: (error "A non-linear term was asserted to arithmetic in a linear logic.")
; EXIT: 1
(declare-sort $$unsorted 0)
(assert (not (forall ((X Int)) (= (* X X) (to_real 1)))))
(set-info :filename scrub.09)
(check-sat-assuming ( true ))
