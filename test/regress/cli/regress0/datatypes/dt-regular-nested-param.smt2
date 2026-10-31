; EXPECT: sat
(set-logic ALL)
(declare-datatype Option (par (X) ((none) (some (val X)))))
(declare-datatypes ((P 2) (Q 1)) (
  (par (X Y) ((p0) (p1 (p1a (P Y X)) (p1b (Q X)) (p1d (Q (Option Int))))))
  (par (Z) ((q0) (q1 (q1a (Q Z)) (q1b (Option Z)) (q1c (P Z Int)))))
))
(declare-const x (P Bool Int))
(assert ((_ is p1) x))
(assert ((_ is q1) (p1b x)))
(assert ((_ is p1) (q1c (p1b x))))
(check-sat)
