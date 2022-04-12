(set-logic ALL)
(set-info :status sat)
(assert (str.in_re "" (re.* (re.range "b" "a"))))
(check-sat)
