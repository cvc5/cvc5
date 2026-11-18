; EXPECT: sat
(set-logic ALL)
(declare-const x Int)
(assert (exists ((s String) (t Int)) (and (= 1 (str.len (str.++ (str.substr s 0 1) (str.at s t)))) (not (str.suffixof (ite (str.in_re "/" (str.to_re s)) (str.substr s 0 x) (str.replace "/" s "")) s)))))
(check-sat)
