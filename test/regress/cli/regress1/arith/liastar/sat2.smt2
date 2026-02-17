; REQUIRES: normaliz
(set-logic HO_ALL)
(set-info :status sat)

(declare-const v1_x Int)
(declare-const v1_y Int)
(declare-const v1_z Int)
(declare-const v2_x Int)
(declare-const v2_y Int)
(declare-const v2_z Int)
(declare-const v3_x Int)
(declare-const v3_y Int)
(declare-const v3_z Int)

(assert (distinct v1_x v1_y v1_z v2_x v2_y v2_z v3_x v3_y v3_z))
(assert (int.star-contains (lambda ((x Int) (y Int) (z Int)) (= x (+ y z))) v1_x v1_y v1_z))
(assert (int.star-contains (lambda ((x Int) (y Int) (z Int)) (= x (+ y z))) v2_x v2_y v2_z))
(assert (int.star-contains (lambda ((x Int) (y Int) (z Int)) (= x (+ y z))) v3_x v3_y v3_z))

(check-sat)
