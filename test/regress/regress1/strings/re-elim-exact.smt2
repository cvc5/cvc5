(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(set-option :re-elim true)
(declare-fun x () String)

(assert (str.in.re x (re.++ re.allchar (str.to.re "A") re.allchar (str.to.re "B") re.allchar)))

(check-sat)
