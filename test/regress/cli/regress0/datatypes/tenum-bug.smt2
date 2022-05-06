(set-logic QF_ALL)
(set-info :status sat)

(declare-datatypes ((DNat 0) (Nat 0)) (((dnat (data Nat)))
                                       ((succ (pred DNat)) (zero))))

(declare-fun x () Nat)

(assert (not (= x zero)))

(check-sat)
