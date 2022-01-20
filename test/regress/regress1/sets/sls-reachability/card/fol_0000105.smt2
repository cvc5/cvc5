(set-logic ALL)

(set-info :status sat)

; forall b_fs:B. forall b_fr:B. forall a_fq:A. forall a_fp:A. B(b_fs & b_fr & a_fq & a_fp & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_fs () (Set Int))

(assert (set.subset b_fs UNIVERALSET))
(assert (>= (* 2 (set.card b_fs)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fr () (Set Int))

(assert (set.subset b_fr UNIVERALSET))
(assert (>= (* 2 (set.card b_fr)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fq () (Set Int))

(assert (set.subset a_fq UNIVERALSET))
(assert (>= (set.card a_fq) (- n t)))

(declare-fun a_fp () (Set Int))

(assert (set.subset a_fp UNIVERALSET))
(assert (>= (set.card a_fp) (- n t)))


(assert
  (not
    (>=
      (* 2
         (set.card
           (set.inter (set.inter (set.inter (set.inter b_fs b_fr) a_fq) a_fp)
                         (set.minus UNIVERALSET f))))
      (+ (+ n (* 3 t)) 1))))

(check-sat)
