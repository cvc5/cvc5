(set-logic ALL)

(set-info :status unsat)

; forall b_x:B. forall a_w:A. C(b_x & a_w & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_x () (Set Int))

(assert (set.subset b_x UNIVERALSET))
(assert (>= (* 2 (set.card b_x)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_w () (Set Int))

(assert (set.subset a_w UNIVERALSET))
(assert (>= (set.card a_w) (- n t)))


(assert
  (not
    (>= (* 2 (set.card (set.inter (set.inter b_x a_w) (set.minus UNIVERALSET f))))
        (+ (- n t) 1))))

(check-sat)
