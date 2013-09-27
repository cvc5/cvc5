(set-logic QF_S)
(set-info :status unsat)

(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(declare-fun ww () String)
(declare-fun pp () String)
(declare-fun qq () String)

; assoc
(assert (or (= xx (str.++ yy "aa")) (= zz (str.++ yy "aa"))
))
(assert (and (not (= (str.++ xx "bb") (str.++ yy "aa" "bb")))
		    (not (= (str.++ zz "bb") (str.++ yy "aa" "bb")))
))

(check-sat)
