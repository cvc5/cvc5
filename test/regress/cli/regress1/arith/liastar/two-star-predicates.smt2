; REQUIRES: normaliz
(set-logic HO_ALL)
(set-info :status unsat)

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const y1 Int)
(declare-const y2 Int)
(declare-const y3 Int)
(assert (and (not (= x1 y1))
  ; a = b = c = 0 => x1 = x2 = x3 = 0
  (int.star-contains (lambda ((a Int) (b Int) (c Int)) (and (and (= a 0) (= b 0)) (= c 0))) x1 x2 x3)  
  ; a = b = c = 0 => y1 = y2 = y3 = 0
  (int.star-contains (lambda ((a Int) (b Int) (c Int)) (and (and (= a 0) (= b 0)) (= c 0))) y1 y2 y3)))
(check-sat)
