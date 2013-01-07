(benchmark clock_synchro
  :source { Clock Synchronization. Bruno Dutertre (bruno@csl.sri.com) }


  :status unsat
:category { industrial }
:difficulty { 0 }
  :logic QF_LRA
  
  :extrafuns ((x_0 Real))
  :extrafuns ((x_1 Real))
  :extrafuns ((x_2 Real))
  :extrafuns ((x_3 Real))
  :extrafuns ((x_4 Real))
  :extrafuns ((x_5 Real))
  :extrafuns ((x_6 Real))
  :extrafuns ((x_7 Real))
  :extrafuns ((x_8 Real))
  :extrafuns ((x_9 Real))
  :extrafuns ((x_10 Real))
  :extrafuns ((x_11 Real))
  :extrafuns ((x_12 Real))
  :extrafuns ((x_13 Real))
  :extrafuns ((x_14 Real))
  :extrafuns ((x_15 Real))
  :extrafuns ((x_16 Real))
  :extrafuns ((x_17 Real))
  :extrafuns ((x_18 Real))
  :extrafuns ((x_19 Real))
  :extrafuns ((x_20 Real))
  :extrafuns ((x_21 Real))
  :extrafuns ((x_22 Real))
  :extrafuns ((x_23 Real))
  :extrafuns ((x_24 Real))
  :extrafuns ((x_25 Real))
  :extrafuns ((x_26 Real))
  :extrafuns ((x_27 Real))
  :formula
(flet ($cvcl_4 (<= x_7 x_12)) (flet ($cvcl_6 (<= x_10 x_12)) (flet ($cvcl_0 (= x_19 x_12)) (flet ($cvcl_1 (= x_20 x_12)) (flet ($cvcl_2 (not $cvcl_0)) (flet ($cvcl_3 (not $cvcl_1)) (flet ($cvcl_5 (= x_19 (+ (+ x_12 x_13) x_14))) (flet ($cvcl_7 (= x_20 (+ (+ x_12 x_13) x_14))) (flet ($cvcl_10 (not $cvcl_5)) (flet ($cvcl_8 (and $cvcl_4 $cvcl_10)) (flet ($cvcl_11 (not $cvcl_7)) (flet ($cvcl_9 (and $cvcl_6 $cvcl_11)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= x_13 0)) (not (<= x_14 0))) (not (<= x_15 0))) (not (< x_16 (+ x_15 (* (* (+ (* (* x_14 1) (/ 1 2)) 1) 1001) (/ 1 999)))))) (< x_17 (- (* (* (- (- x_14 x_16) 1) 999) (/ 1 2)) 1))) (not (< x_17 (* (* (+ (+ (+ x_13 x_15) x_16) (/ 1501 1000)) 1001) (/ 1 999))))) (not (<= x_18 0))) (<= x_18 (- x_13 (+ (+ x_15 (* (* (+ x_14 2) 1001) (/ 1 999))) (/ 1 2))))) (<= x_0 x_1)) (<= x_0 x_2)) (<= x_1 (+ x_0 (/ 1001 1000)))) (<= x_2 (+ x_0 (/ 1001 1000)))) (<= x_3 x_4)) (<= x_3 x_5)) (<= x_4 (+ x_3 (/ 1001 1000)))) (<= x_5 (+ x_3 (/ 1001 1000)))) (<= (* (* (- x_7 x_8) 999) (/ 1 1000)) (- x_1 x_6))) (<= (* (* (- x_10 x_11) 999) (/ 1 1000)) (- x_2 x_9))) (<= (- x_1 x_6) (* (* (- x_7 x_8) 1001) (/ 1 1000)))) (<= (- x_2 x_9) (* (* (- x_10 x_11) 1001) (/ 1 1000)))) (<= (- x_12 x_17) x_21)) (<= (- x_12 x_17) x_22)) (<= x_21 (- x_12 x_18))) (<= x_22 (- x_12 x_18))) (<= (- x_21 x_21) x_16)) (<= (- x_22 x_21) x_16)) (<= (- x_21 x_22) x_16)) (<= (- x_22 x_22) x_16)) (or (and $cvcl_0 (<= x_7 x_25))  $cvcl_5 )) (or (and $cvcl_1 (<= x_10 x_25))  $cvcl_7 )) (or $cvcl_0  $cvcl_1 )) (or $cvcl_2  (and (<= (* (* (- x_7 x_21) 999) (/ 1 1000)) (- x_1 x_4)) (<= (- x_1 x_4) (* (* (- x_7 x_21) 1001) (/ 1 1000)))) )) (or $cvcl_3  (and (<= (* (* (- x_10 x_22) 999) (/ 1 1000)) (- x_2 x_5)) (<= (- x_2 x_5) (* (* (- x_10 x_22) 1001) (/ 1 1000)))) )) (or (or $cvcl_2  $cvcl_4 )  (and (and (not (< x_0 x_23)) (<= (* (* (- x_7 x_12) 999) (/ 1 1000)) (- x_1 x_23))) (<= (- x_1 x_23) (* (* (- x_7 x_12) 1001) (/ 1 1000)))) )) (or (or $cvcl_3  $cvcl_6 )  (and (and (not (< x_0 x_24)) (<= (* (* (- x_10 x_12) 999) (/ 1 1000)) (- x_2 x_24))) (<= (- x_2 x_24) (* (* (- x_10 x_12) 1001) (/ 1 1000)))) )) (or $cvcl_8  (and (<= x_26 (+ (+ (* (* (+ (+ (+ x_21 (* (* (- x_23 x_4) 1000) (/ 1 999))) x_22) (* (* (- x_23 x_5) 1000) (/ 1 999))) 1) (/ 1 2)) x_15) (/ 3001 1998))) (not (< x_26 (- (- (* (* (+ (+ (+ x_21 (* (* (- x_23 x_4) 1000) (/ 1 1001))) x_22) (* (* (- x_23 x_5) 1000) (/ 1 1001))) 1) (/ 1 2)) x_15) (/ 1 2))))) )) (or $cvcl_9  (and (<= x_27 (+ (+ (* (* (+ (+ (+ x_21 (* (* (- x_24 x_4) 1000) (/ 1 999))) x_22) (* (* (- x_24 x_5) 1000) (/ 1 999))) 1) (/ 1 2)) x_15) (/ 3001 1998))) (not (< x_27 (- (- (* (* (+ (+ (+ x_21 (* (* (- x_24 x_4) 1000) (/ 1 1001))) x_22) (* (* (- x_24 x_5) 1000) (/ 1 1001))) 1) (/ 1 2)) x_15) (/ 1 2))))) )) (or $cvcl_8  (and (<= (* (* (- x_12 x_21) 999) (/ 1 1000)) (- x_23 x_4)) (<= (- x_23 x_4) (* (* (- x_12 x_21) 1001) (/ 1 1000)))) )) (or $cvcl_9  (and (<= (* (* (- x_12 x_22) 999) (/ 1 1000)) (- x_24 x_5)) (<= (- x_24 x_5) (* (* (- x_12 x_22) 1001) (/ 1 1000)))) )) (or $cvcl_10  (= x_8 (+ x_26 x_14)) )) (or $cvcl_11  (= x_11 (+ x_27 x_14)) )) (or $cvcl_10  (and (<= (* (* x_14 999) (/ 1 1000)) (- x_6 x_23)) (<= (- x_6 x_23) (* (* x_14 1001) (/ 1 1000)))) )) (or $cvcl_11  (and (<= (* (* x_14 999) (/ 1 1000)) (- x_9 x_24)) (<= (- x_9 x_24) (* (* x_14 1001) (/ 1 1000)))) )) (= x_25 (+ x_12 x_14))) (or (or (or (not (<= (- x_7 x_7) (+ (+ (+ x_15 x_16) (* (* (+ x_17 x_14) 2) (/ 1 999))) (/ 2335 666))))  (not (<= (- x_10 x_7) (+ (+ (+ x_15 x_16) (* (* (+ x_17 x_14) 2) (/ 1 999))) (/ 2335 666)))) )  (not (<= (- x_7 x_10) (+ (+ (+ x_15 x_16) (* (* (+ x_17 x_14) 2) (/ 1 999))) (/ 2335 666)))) )  (not (<= (- x_10 x_10) (+ (+ (+ x_15 x_16) (* (* (+ x_17 x_14) 2) (/ 1 999))) (/ 2335 666)))) ))))))))))))))
)
