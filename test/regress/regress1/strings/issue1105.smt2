(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-option :strings-exp true)
(set-info :status sat)
(declare-datatypes () ((Val
    (Str (str String))
    (Num (num Int)))))

(declare-const var0 Val)
(assert (=> (is-Str var0) (distinct (str.to.int (str var0)) (- 1))))
(check-sat)
