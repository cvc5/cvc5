; COMMAND-LINE: --deep-restart=input -o deep-restart
; EXPECT: (deep-restart ((= f k)))
; EXPECT: sat
(set-logic ALL)
(set-option :deep-restart input)
(declare-const x Bool)
(declare-fun b () Int)
(declare-fun f () String)
(declare-fun k () String)
(assert (ite (distinct b 0) (= (str.++ k f) (str.++ k k)) x))
(assert (distinct true (= b 0)))
(check-sat)
