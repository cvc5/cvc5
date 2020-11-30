(set-info :smt-lib-version 2.6)
(set-logic SLIA)
(set-info :status unsat)

(declare-fun x () String)
(assert (str.in_re x (re.++ (str.to_re "baa") (re.* (str.to_re "a")) (re.* (str.to_re "c")))))

(declare-fun y () String)
(assert (< (str.len y) 2))

(assert (or
(not (str.in_re x (re.++ (str.to_re "baa") (re.* (str.to_re "a")) (re.* (str.to_re "a")) (re.* (str.to_re "c")))))
(not (str.in_re x (re.++ (str.to_re "ba") (str.to_re "") (re.* (str.to_re "a")) (str.to_re "a") (re.* (str.to_re "c")))))
(not (str.in_re x (re.++ (str.to_re "b") (re.* (str.to_re "a")) (str.to_re "a") (re.* (str.to_re "a")) (str.to_re "a") (re.* (str.to_re "c")))))

(str.in_re y (re.++ re.allchar re.allchar (re.* re.allchar) re.allchar))
(str.in_re y (re.++ re.allchar re.allchar re.allchar))
)
)

(check-sat)
