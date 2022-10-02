; EXPECT: sat
(set-logic ALL)
(set-option :strings-exp true)
(set-info :status sat)
(declare-datatype Val
    ((Str (str String))
    (Num (num Int))))

(declare-const var0 Val)
(assert (=> (is-Str var0) (distinct (str.to_int (str var0)) (- 1))))
(check-sat)
