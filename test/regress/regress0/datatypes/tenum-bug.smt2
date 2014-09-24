(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)

(declare-datatypes () ((DNat (dnat (data Nat)))
                       (Nat (succ (pred DNat)) (zero))))

(declare-fun x () Nat)

(assert (not (= x zero)))

(check-sat)