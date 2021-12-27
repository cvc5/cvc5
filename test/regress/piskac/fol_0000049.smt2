(set-logic ALL)
(set-info :status unsat)

; forall c_bb:C. forall b_ba:B. forall a_z:A. c_bb + b_ba + a_z + |~f| - 3n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bb () Int)
(assert (<= c_bb n))
(assert (>= c_bb 0))
(assert (>= (* 2 c_bb) (+ (- n t) 1)))

(declare-fun b_ba () Int)
(assert (<= b_ba n))
(assert (>= b_ba 0))
(assert (>= (* 2 b_ba) (+ (+ n (* 3 t)) 1)))

(declare-fun a_z () Int)
(assert (<= a_z n))
(assert (>= a_z 0))
(assert (>= a_z (- n t)))


(assert (and (< (* 2 (- (+ (+ (+ c_bb b_ba) a_z) (set.card (set.minus UNIVERALSET f))) (* 3 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
