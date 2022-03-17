; SCRUBBER: sed -e 's/(>=.*/learned-ineq/'
; EXPECT: sat
; EXPECT: (
; EXPECT: learned-ineq
; EXPECT: learned-ineq
; EXPECT: )
(set-logic ALL)
(set-option :produce-learned-literals true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x 5))
(assert (< y 4))
(assert (or (< x y) (> z 0)))
(check-sat)
(get-learned-literals)