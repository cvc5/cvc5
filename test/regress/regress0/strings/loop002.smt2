(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= (str.++ x "ba") (str.++ "ab" x)))

(check-sat)
