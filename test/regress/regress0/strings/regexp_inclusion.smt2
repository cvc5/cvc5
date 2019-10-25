; COMMAND-LINE: --strings-exp --no-re-elim
(set-info :status unsat)
(set-logic ALL)
(declare-const actionName String)

(assert
(str.in.re actionName (re.++ (str.to.re "wiz") (re.* re.allchar) (str.to.re "foobar") (re.* re.allchar) (str.to.re "baz/") (re.* re.allchar))))

(assert (not
(str.in.re actionName (re.++ (str.to.re "wiz") (re.* re.allchar) (re.++ (str.to.re "foo") re.allchar (str.to.re "ar")) (re.* re.allchar) (str.to.re "baz/") (re.* re.allchar)))
))

(check-sat)
