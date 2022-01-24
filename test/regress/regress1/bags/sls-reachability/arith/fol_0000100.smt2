(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_eb:C. forall b_ea:B. forall a_dz:A. c_eb + 2b_ea + 2a_dz + |~f| - 5n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_eb () Int)

(assert (<= c_eb n))
(assert (>= c_eb 0))
(assert (>= (* 2 c_eb) (+ (- n t) 1)))

(declare-fun b_ea () Int)

(assert (<= b_ea n))
(assert (>= b_ea 0))
(assert (>= (* 2 b_ea) (+ (+ n (* 3 t)) 1)))

(declare-fun a_dz () Int)

(assert (<= a_dz n))
(assert (>= a_dz 0))
(assert (>= a_dz (- n t)))


(assert
 (and
  (<
   (-
    (+ (+ (+ c_eb (* 2 b_ea)) (* 2 a_dz))
       (bag.card (bag.difference_subtract UNIVERALSET f)))
    (* 5 n))
   1)
  (> 1 0)))

(check-sat)
