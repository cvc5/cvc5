; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (not (str.in_re (str.replace_re a (re.++ (re.* (re.union (str.to_re "a") (str.to_re ""))) (str.to_re "b")) "") (str.to_re ""))))
(assert (ite (str.in_re a (re.diff (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.range "a" "u")))
    (str.in_re a (re.diff (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.range "a" "u")))
    (str.<= a "b")))
(set-info :status sat)
(check-sat)
