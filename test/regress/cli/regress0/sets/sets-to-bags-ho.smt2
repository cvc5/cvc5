; COMMAND-LINE: --sets-to-bags=setof
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun A () (Set Int))
(assert (set.member 1 A))
(assert (set.all (lambda ((y Int)) (> y 0)) (set.map (lambda ((y Int)) (+ y 1)) A)))
(assert (set.some (lambda ((y Int)) (= y 2)) (set.filter (lambda ((y Int)) (> y 1)) (set.map (lambda ((y Int)) (+ y 1)) A))))
(assert (= (set.fold (lambda ((y Int) (acc Int)) (+ y acc)) 0 A) 1))
(check-sat)
