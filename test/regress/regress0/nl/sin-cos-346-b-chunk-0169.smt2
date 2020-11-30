; COMMAND-LINE: --no-check-models --nl-ext-tplanes
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoSQ3 skoSQ3))) (and (not (<= (* skoX (* skoX (* skoX (* skoX (+ (/ 1 24) (* skoX (* skoX (+ (/ (- 1) 720) (* skoX (* skoX (/ 1 40320))))))))))) (+ (- 3) ?v_0))) (and (= ?v_0 3) (and (not (<= (+ (/ (- 1) 10000000) (* pi (/ 1 2))) skoX)) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (not (<= skoX 0)) (not (<= skoSQ3 0))))))))))
(check-sat)
(exit)
