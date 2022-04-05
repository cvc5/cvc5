(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(assert
 (<
 (* a
  (/ 1
  (/ (- 2) a
   (- a
   (* a
    (mod (to_int a)
    (to_int
     (/ a
     (* a
      (div (to_int (/ (- 9) 800))
      (to_int (/ a a))))))))))))
 (- a)))
(assert (<= 0 a))
(check-sat)
