(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(set-option :re-elim on)
(declare-fun x () String)

(assert (str.in_re x (re.++ re.allchar (str.to_re "A") re.allchar (str.to_re "B") re.allchar)))

(check-sat)
