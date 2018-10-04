; COMMAND-LINE: --lang=smt2.5 --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)

(declare-datatypes () ((Unit (uu))))

(declare-fun y () Int)
(declare-fun b () Bool)
(declare-fun s () (Set Int))
(declare-fun u () Unit)

(assert (= s (insert y s)))
(assert (=> b (= uu u)))

(push 1)
(check-sat)
(pop 1)

(push 1)
(check-sat)
