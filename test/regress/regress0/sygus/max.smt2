; EXPECT: unsat
; COMMAND-LINE: --cegqi

(set-logic UFDTLIA)

(declare-datatypes () ((start (startx)
                              (starty)
                              (start1)
                              (start0)
                              (startplus (startplus1 start) (startplus2 start))
                              (startminus (startminus1 start) (startminus2 start))
                              (startite (startite1 startbool) (startite2 start) (startite3 start)))
                       (startbool (startand (startand1 startbool) (startand2 startbool))
                                  (startor (startor1 startbool) (startor2 startbool))
                                  (startnot (startnot1 startbool))
                                  (startleq (startleq1 start) (startleq2 start))
                                  (starteq (starteq1 start) (starteq2 start))
                                  (startgeq (startgeq1 start) (startgeq2 start))
                                  )))

(declare-fun eval (start Int Int) Int)
(declare-fun evalbool (startbool Int Int) Bool)

(assert (forall ((x Int) (y Int)) (! (= (eval startx x y) x) :pattern ((eval startx x y)))))
(assert (forall ((x Int) (y Int)) (! (= (eval starty x y) y) :pattern ((eval starty x y)))))
(assert (forall ((x Int) (y Int)) (! (= (eval start0 x y) 0) :pattern ((eval start0 x y)))))
(assert (forall ((x Int) (y Int)) (! (= (eval start1 x y) 1) :pattern ((eval start1 x y)))))
(assert (forall ((s1 start) (s2 start) (x Int) (y Int)) (! (= (eval (startplus s1 s2) x y) (+ (eval s1 x y) (eval s2 x y))) :pattern ((eval (startplus s1 s2) x y)))))
(assert (forall ((s1 start) (s2 start) (x Int) (y Int)) (! (= (eval (startminus s1 s2) x y) (- (eval s1 x y) (eval s2 x y))) :pattern ((eval (startminus s1 s2) x y)))))
(assert (forall ((s1 startbool) (s2 start) (s3 start) (x Int) (y Int)) (! (= (eval (startite s1 s2 s3) x y) (ite (evalbool s1 x y) (eval s2 x y) (eval s3 x y)))
                                                                          :pattern ((eval (startite s1 s2 s3) x y)))))

(assert (forall ((s1 startbool) (s2 startbool) (x Int) (y Int)) (! (= (evalbool (startand s1 s2) x y) (and (evalbool s1 x y) (evalbool s2 x y)))
                                                                   :pattern ((evalbool (startand s1 s2) x y)))))
(assert (forall ((s1 startbool) (s2 startbool) (x Int) (y Int)) (! (= (evalbool (startor s1 s2) x y) (or (evalbool s1 x y) (evalbool s2 x y)))
                                                                   :pattern ((evalbool (startor s1 s2) x y)))))
(assert (forall ((s1 startbool) (x Int) (y Int)) (! (= (evalbool (startnot s1) x y) (not (evalbool s1 x y)))
                                                    :pattern ((evalbool (startnot s1) x y)))))
(assert (forall ((s1 start) (s2 start) (x Int) (y Int)) (! (= (evalbool (startleq s1 s2) x y) (<= (eval s1 x y) (eval s2 x y)))
                                                           :pattern ((evalbool (startleq s1 s2) x y)))))
(assert (forall ((s1 start) (s2 start) (x Int) (y Int)) (! (= (evalbool (starteq s1 s2) x y) (= (eval s1 x y) (eval s2 x y)))
                                                           :pattern ((evalbool (starteq s1 s2) x y)))))
(assert (forall ((s1 start) (s2 start) (x Int) (y Int)) (! (= (evalbool (startgeq s1 s2) x y) (>= (eval s1 x y) (eval s2 x y)))
                                                           :pattern ((evalbool (startgeq s1 s2) x y)))))


(define-fun P ((fmax start) (x Int) (y Int)) Bool (and (>= (eval fmax x y) x) (>= (eval fmax x y) y) (or (= (eval fmax x y) x) (= (eval fmax x y) y))))

(assert (forall ((fmax start)) (! (exists ((x Int) (y Int)) (not (P fmax x y))) :sygus)))


(check-sat)
