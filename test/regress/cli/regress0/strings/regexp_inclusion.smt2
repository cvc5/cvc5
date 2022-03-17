; COMMAND-LINE: --strings-exp
(set-info :status unsat)
(set-logic ALL)
(declare-const actionName String)

(assert
(str.in_re actionName (re.++ (str.to_re "wiz") (re.* re.allchar) (str.to_re "foobar") (re.* re.allchar) (str.to_re "baz/") (re.* re.allchar))))

(assert (not
(str.in_re actionName (re.++ (str.to_re "wiz") (re.* re.allchar) (re.++ (str.to_re "foo") re.allchar (str.to_re "ar")) (re.* re.allchar) (str.to_re "baz/") (re.* re.allchar)))
))

(check-sat)
