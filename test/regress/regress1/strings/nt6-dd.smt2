; COMMAND-LINE: --strings-exp --re-elim
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(declare-const resource_resource String)
(declare-const p1.0.resource Bool)

(assert (str.in.re resource_resource (re.++ (str.to.re "ab") (re.* re.allchar) (str.to.re "b") )))

(assert (= p1.0.resource (str.in.re resource_resource (re.++ (str.to.re "a") (re.* re.allchar) (str.to.re "b") ))))

(check-sat)
