(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_dn:C. forall a_dm:A. c_dn + a_dm + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dn () Int)

(assert (<= c_dn n))
(assert (>= c_dn 0))
(assert (>= (* 2 c_dn) (+ (- n t) 1)))

(declare-fun a_dm () Int)

(assert (<= a_dm n))
(assert (>= a_dm 0))
(assert (>= a_dm (- n t)))


(assert (and (< (- (+ (+ c_dn a_dm) (bag.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
