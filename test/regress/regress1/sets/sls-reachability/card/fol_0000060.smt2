(set-logic ALL)

(set-info :status unsat)

; forall a_bw:A. C(a_bw & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bw () (Set Int))

(assert (set.subset a_bw UNIVERALSET))
(assert (>= (set.card a_bw) (- n t)))


(assert
  (not
    (>= (* 2 (set.card (set.inter a_bw (set.minus UNIVERALSET f)))) (+ (- n t) 1))))

(check-sat)
