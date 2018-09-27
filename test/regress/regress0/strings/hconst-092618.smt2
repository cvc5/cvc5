(set-logic ALL)
(declare-fun x () String)
(assert (str.contains "::" (str.++ x ":" x ":")))
(check-sat)