(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cj:C. forall b_ci:B. c_cj + b_ci + |f & ~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cj () Int)

(assert (<= c_cj n))
(assert (>= c_cj 0))
(assert (>= (* 2 c_cj) (+ (- n t) 1)))

(declare-fun b_ci () Int)

(assert (<= b_ci n))
(assert (>= b_ci 0))
(assert (>= (* 2 b_ci) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (<
   (-
    (+ (+ c_cj b_ci)
       (bag.card (bag.inter_min f (bag.difference_subtract UNIVERALSET f))))
    (* 2 n))
   1)
  (> 1 0)))

(check-sat)
