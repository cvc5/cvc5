; COMMAND-LINE: --tlimit-per=500
; EXPECT: unknown
(set-logic ALL)
(set-option :produce-proofs true)
(set-option :proof-check eager)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_2 (<= 0 skoY))(?v_0 (* skoX (- 1)))) (let ((?v_3 (* skoZ (+ 1 0)))(?v_4 (<= 0 (+ skoX skoY)))) (let ((?v_1 (not ?v_4))(?v_5 (* skoX ?v_0))) (let ((?v_6 (* skoY (* skoX (+ 0 ?v_5))))) (and (<= 0 0) (and ?v_1 (and (or ?v_1 (is_int ?v_0)) (and (or ?v_2 (<= ?v_3 (+ 0 (* (- 0 ?v_3) (+ 0 ?v_0))))) (and (or (not ?v_2) (>= 3 (+ (+ 3 (* skoX skoX)) ?v_6))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (>= skoZ ?v_6)) (not (<= (- (+ ?v_5 skoZ)) skoX)))))))))))))))
(check-sat)
