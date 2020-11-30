; COMMAND-LINE: --strings-exp --re-elim
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-const resource_resource String)
(declare-const p1.0.resource Bool)

(assert (str.in_re resource_resource (re.++ (str.to_re "ab") (re.* re.allchar) (str.to_re "b") )))

(assert (= p1.0.resource (str.in_re resource_resource (re.++ (str.to_re "a") (re.* re.allchar) (str.to_re "b") ))))

(check-sat)
