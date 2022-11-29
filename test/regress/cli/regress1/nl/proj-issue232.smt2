(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(assert
 (<
 (* a
  (/ 1.0
  (/ (- 2.0) a
   (- a
   (* a
    (to_real (mod (to_int a)
    (to_int
     (/ a
     (* a
      (to_real (div (to_int (/ (- 9) 800))
      (to_int (/ a a))))))))))))))
 (- a)))
(assert (<= 0.0 a))
(check-sat)
