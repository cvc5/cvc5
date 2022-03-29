; COMMAND-LINE: --strings-exp
(set-info :status sat)
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)

(assert (str.in_re x (re.++ (str.to_re "bar") (re.* re.allchar) (str.to_re "bar"))))
(assert (str.in_re x (re.++ (str.to_re "ba") re.allchar (re.* re.allchar) (str.to_re "bar"))))

(assert (not (str.in_re y (re.++ (str.to_re "bar") (re.* re.allchar) (str.to_re "bar")))))
(assert (not (str.in_re y (re.++ (str.to_re "ba") re.allchar (re.* re.allchar) (str.to_re "bar")))))
(assert (not (= y "")))

(check-sat)
