; COMMAND-LINE: --sygus-inference=try -q
(set-logic LIA)
(set-info :status sat)
(assert (forall ((x Int) (y Int)) (or (<= x (+ y 1)) (exists ((z Int)) (and (> z y) (< z x))))))
(check-sat)
