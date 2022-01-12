; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)

(declare-datatypes ((Unit 0)) (((uu))))

(declare-fun y () Int)
(declare-fun b () Bool)
(declare-fun s () (Set Int))
(declare-fun u () Unit)

(assert (= s (set.insert y s)))
(assert (=> b (= uu u)))

(push 1)
(check-sat)
(pop 1)

(push 1)
(check-sat)
