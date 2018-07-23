(set-info :smt-lib-version 2.5)
(set-logic SLIA)
(set-info :status unsat)
(declare-fun x () String)

(assert (str.in.re x (re.++ (str.to.re "baa") (re.* (str.to.re "a")) (re.* (str.to.re "c")))))

(assert (or
(not (str.in.re x (re.++ (str.to.re "baa") (re.* (str.to.re "a")) (re.* (str.to.re "a")) (re.* (str.to.re "c")))))
(not (str.in.re x (re.++ (str.to.re "ba") (str.to.re "") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "c")))))
(not (str.in.re x (re.++ (str.to.re "b") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "a")) (str.to.re "a") (re.* (str.to.re "c")))))
)
) 

(check-sat)
