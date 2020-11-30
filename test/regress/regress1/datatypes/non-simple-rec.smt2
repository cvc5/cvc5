; COMMAND-LINE: --dt-nested-rec
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((T 0)) (((Nil) (Map (m (Array Int T)) ) ) ))
(declare-fun a () T)
(declare-fun b () T)
(declare-fun c () T)
(declare-fun d () T)
(assert (distinct a b c d))
(check-sat)
