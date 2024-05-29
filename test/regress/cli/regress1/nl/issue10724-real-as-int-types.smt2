; COMMAND-LINE: --solve-real-as-int -q
; EXPECT: sat
(set-logic ALL)
(declare-fun v () Real)
(assert (and (forall ((a Real)) ((_ divisible 3) (set.choose (set.singleton (to_int (arcsin v))))))))
(check-sat)
