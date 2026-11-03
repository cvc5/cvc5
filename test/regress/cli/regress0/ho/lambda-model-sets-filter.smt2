; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic HO_ALL)
(declare-const y Int)
(declare-const z Int)
(declare-const S (Set Int))
(declare-const T (Set Int))
; The two lambdas are equal but syntactically distinct. They are in the same
; equivalence class of the equality engine of sets, which should not lead to
; distinct lambda values in the same equivalence class of the model.
(assert (= (lambda ((x Int)) (> x y)) (lambda ((x Int)) (> x z))))
(assert (set.member 1 S))
(assert (= T (set.filter (lambda ((x Int)) (> x y)) S)))
(assert (= T (set.filter (lambda ((x Int)) (> x z)) S)))
(assert (set.member 1 T))
(check-sat)
