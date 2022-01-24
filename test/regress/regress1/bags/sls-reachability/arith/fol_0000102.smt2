(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_eg:C. forall b_ef:B. forall a_ee:A. c_eg + 2b_ef + a_ee + |~f| - 4n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_eg () Int)

(assert (<= c_eg n))
(assert (>= c_eg 0))
(assert (>= (* 2 c_eg) (+ (- n t) 1)))

(declare-fun b_ef () Int)

(assert (<= b_ef n))
(assert (>= b_ef 0))
(assert (>= (* 2 b_ef) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ee () Int)

(assert (<= a_ee n))
(assert (>= a_ee 0))
(assert (>= a_ee (- n t)))


(assert
 (and
  (<
   (-
    (+ (+ (+ c_eg (* 2 b_ef)) a_ee) (bag.card (bag.difference_subtract UNIVERALSET f)))
    (* 4 n))
   1)
  (> 1 0)))

(check-sat)
