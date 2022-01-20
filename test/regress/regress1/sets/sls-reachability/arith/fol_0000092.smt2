(set-logic ALL)
(set-info :status unsat)

; forall c_dn:C. forall a_dm:A. c_dn + a_dm + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dn () Int)
(assert (<= c_dn n))
(assert (>= c_dn 0))
(assert (>= (* 2 c_dn) (+ (- n t) 1)))

(declare-fun a_dm () Int)
(assert (<= a_dm n))
(assert (>= a_dm 0))
(assert (>= a_dm (- n t)))


(assert (and (< (- (+ (+ c_dn a_dm) (set.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
