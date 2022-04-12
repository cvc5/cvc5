; EXPECT: sat
; COMMAND-LINE: --sygus-inference -q
(set-logic ALL)
(assert
 (forall ((a Real))
  (exists ((b Real))
   (exists ((c Real))
    (and
     (< (+ a c) 0.0)
     (or (distinct a 0.0) (= b 5.0))
     (distinct (+ b c) 1.0)
     (< c 1.0))))))
(check-sat)
