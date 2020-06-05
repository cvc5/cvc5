; COMMAND-LINE: --dt-nested-rec
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((T 1)) (
(par (x) ((Data (s x)) (Map (m (Array Int (T (T Int)))) ) ) ))
)
(declare-fun a () (T Int))
(declare-fun b () (T Int))
(declare-fun c () (T Int))
(declare-fun d () (T Int))
(assert (distinct a b c d))
(assert (= (select (m a) 5) (Data b)))
(assert (not (= (s b) 0)))
(check-sat)
