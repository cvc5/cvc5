(set-logic ALL)

(set-info :status sat)

; forall c_ck:C. forall b_cj:B. forall b_ci:B. nonempty(c_ck & b_cj & b_ci & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ck () (Set Int))

(assert (set.subset c_ck UNIVERALSET))
(assert (>= (* 2 (set.card c_ck)) (+ (- n t) 1)))

(declare-fun b_cj () (Set Int))

(assert (set.subset b_cj UNIVERALSET))
(assert (>= (* 2 (set.card b_cj)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ci () (Set Int))

(assert (set.subset b_ci UNIVERALSET))
(assert (>= (* 2 (set.card b_ci)) (+ (+ n (* 3 t)) 1)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter c_ck b_cj) b_ci) (set.minus UNIVERALSET f)))
    0))

(check-sat)
