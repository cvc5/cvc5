; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: sat
(set-logic QF_NIRA)
(set-info :status sat)
(declare-fun pi () Real)

(assert (and (< 3.0 pi) (< pi 3.5)))

(declare-fun y () Real)
(assert (and (<= (- pi) y) (<= y pi)))

(declare-fun s () Int)

(declare-fun z () Real)

(assert (= z (* 2.0 pi (to_real s))))

(assert (> z 60.0))

(check-sat)
