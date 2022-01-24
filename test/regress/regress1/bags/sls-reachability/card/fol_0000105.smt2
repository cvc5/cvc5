(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_fs:B. forall b_fr:B. forall a_fq:A. forall a_fp:A. B(b_fs & b_fr & a_fq & a_fp & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_fs () (Bag Int))

(assert (bag.subbag b_fs UNIVERALSET))
(assert (>= (* 2 (bag.card b_fs)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fr () (Bag Int))

(assert (bag.subbag b_fr UNIVERALSET))
(assert (>= (* 2 (bag.card b_fr)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fq () (Bag Int))

(assert (bag.subbag a_fq UNIVERALSET))
(assert (>= (bag.card a_fq) (- n t)))

(declare-fun a_fp () (Bag Int))

(assert (bag.subbag a_fp UNIVERALSET))
(assert (>= (bag.card a_fp) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min
        (bag.inter_min (bag.inter_min (bag.inter_min b_fs b_fr) a_fq) a_fp)
        (bag.difference_subtract UNIVERALSET f))))
   (+ (+ n (* 3 t)) 1))))

(check-sat)
