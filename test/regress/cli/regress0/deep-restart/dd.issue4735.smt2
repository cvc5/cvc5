; COMMAND-LINE: --deep-restart=input
; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(declare-fun b () Int)
(declare-fun f () String)
(declare-fun k () String)
(assert (ite (distinct b 0) (= (str.++ k f) (str.++ k k)) x))
(assert (distinct true (= b 0)))
(check-sat)
