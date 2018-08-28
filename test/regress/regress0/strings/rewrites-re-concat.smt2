(set-info :smt-lib-version 2.5)
(set-logic SLIA)
(set-info :status unsat)

(declare-fun x () String)
(assert (str.in.re x (re.++ (str.to.re "baa") (re.* (str.to.re "a")) (re.* (str.to.re "c")))))

(declare-fun y () String)
(assert (< (str.len y) 2))

(assert (or
(not (str.in.re x (re.++ (str.to.re "baa") (re.* (str.to.re "a")) (re.* (str.to.re "a")) (re.* (str.to.re "c")))))
(not (str.in.re x (re.++ (str.to.re "ba") (str.to.re "") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "c")))))
(not (str.in.re x (re.++ (str.to.re "b") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "c")))))

(str.in.re y (re.++ re.allchar re.allchar (re.* re.allchar) re.allchar))
(str.in.re y (re.++ re.allchar re.allchar re.allchar))
)
)

(check-sat)
