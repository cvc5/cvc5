; COMMAND-LINE: --decision=justification
; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(set-option :produce-proofs true)
(set-option :proof-check eager)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_2 (<= 0 skoY)) (?v_0 (* skoX (- 1)))) (let ((?v_3 (* skoZ (+ 1 (* skoY ?v_0)))) (?v_4 (<= (* skoZ (+ (- 1) (* skoY skoX))) (+ skoX skoY)))) (let ((?v_1 (not ?v_4)) (?v_5 (* skoX ?v_0))) (let ((?v_6 (* skoY (* skoX (+ (- 3) ?v_5))))) (and (<= ?v_3 (+ ?v_0 (* skoY (- 1)))) (and ?v_1 (and (or ?v_1 ?v_2) (and (or ?v_2 (<= ?v_3 (+ (+ 1 ?v_0) (* skoY (+ (- 1) ?v_0))))) (and (or (not ?v_2) (or ?v_4 (<= (* skoZ (+ (+ 3 (* skoX skoX)) ?v_6)) (+ (* skoX ?v_5) (* skoY (+ (* skoX (* skoX (- 3))) ?v_6)))))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX)))))))))))))))
(check-sat)
(exit)
