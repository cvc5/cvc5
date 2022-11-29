; SCRUBBER: sed -e 's/(error.*/error/'
; COMMAND-LINE: -i --bitblast=eager
; EXPECT: error
; EXIT: 1
(set-logic BV)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (forall ((c Bool) (d Bool)) (or (and a d) (and b d) (and c d))))
(check-sat)
