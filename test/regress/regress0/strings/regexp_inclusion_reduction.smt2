; COMMAND-LINE: --strings-exp --no-re-elim
(set-info :status sat)
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.++ (str.to.re "bar") (re.* re.allchar) (str.to.re "bar"))))
(assert (str.in.re x (re.++ (str.to.re "ba") re.allchar (re.* re.allchar) (str.to.re "bar"))))

(assert (not (str.in.re y (re.++ (str.to.re "bar") (re.* re.allchar) (str.to.re "bar")))))
(assert (not (str.in.re y (re.++ (str.to.re "ba") re.allchar (re.* re.allchar) (str.to.re "bar")))))
(assert (not (= y "")))

(check-sat)
