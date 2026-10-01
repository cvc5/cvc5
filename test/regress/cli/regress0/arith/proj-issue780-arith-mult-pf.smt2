; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun skoX () Real) (declare-fun skoY () Real) (declare-fun skoZ () Real) 
(assert (let ((?v_2 (<= 0 skoY))(?v_0 (* skoX (- 1)))) (let ((?v_3 0)(?v_4 (<= (* skoZ
 (+ 0 (* skoY skoX))) 0))) (let ((?v_1 (not ?v_4))(?v_5 0)) (let ((?v_6 (* skoY (* skoX (+ (- 3) ?v_5))))) 
(and (<= 0 0) (and ?v_1 (and (or ?v_1 ?v_2) (and (< (+ (+ 3 (* skoX skoX)) ?v_6) 1) (and
 (or (not ?v_2) (or (< 0 ?v_0) (<= (* (to_real (- (to_int ?v_0))) (* (+ (+ 3 (* skoX skoX)) ?v_6) (- 3)))
 (+ (+ (+ (* skoX ?v_5) (* skoY (+ (* skoX (* skoX (- 3))) ?v_6))) (+ ?v_0 (* skoY (- 1)))) (to_real (+ 
(- 1) ?v_0)))))) (and (< (- 1) (+ (+ 1 ?v_0) (* skoY (+ (- 1) (* (* skoY (+ (- 3) (+ 1 ?v_0))) ?v_5))))) 
(and (not (<= (+ ?v_5 skoY) (- 1))) (and (not (=> (<= ?v_0 skoY) (<= skoZ 0))) (not (<= skoY ?v_6)))))))))))))))
 (check-sat)
(exit)
