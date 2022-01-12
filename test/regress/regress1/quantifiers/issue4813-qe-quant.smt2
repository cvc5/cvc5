; EXPECT: v24
(set-logic LIA)
(declare-const v8 Bool)
(assert (not (exists ((q16 Bool)) (xor true q16 v8 q16))))
(declare-const v24 Bool)
(get-qe (exists ((q17 Bool) (q18 Int) (q19 Int) (q20 Int) (q21 Int) (q22 Bool)) v24))
