; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)

(declare-datatypes ((Unit 0)) (((uu))))

(declare-fun y () Int)
(declare-fun b () Bool)
(declare-fun s () (Bag Int))
(declare-fun u () Unit)

(assert (= s (bag.union_max (bag y 1) s)))
(assert (=> b (= uu u)))

(push 1)
(check-sat)
(pop 1)

(push 1)
(check-sat)
