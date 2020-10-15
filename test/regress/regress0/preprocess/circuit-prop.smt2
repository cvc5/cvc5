; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat

;;;;; iteEvalThen(true)
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert a)
(assert b)
(assert (not (ite a b c)))
(check-sat)

(reset)

;;;;; iteEvalThen(false)
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert a)
(assert (not b))
(assert (or (ite a b c) d))
(check-sat)

(reset)

;;;;; iteEvalElse(true)
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (not a))
(assert c)
(assert (not (ite a b c)))
(check-sat)

(reset)

;;;;; iteEvalElse(false)
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (not a))
(assert (not c))
(assert (or (ite a b c) d))
(check-sat)

(reset)

(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert a)
(assert b)
(assert (=> a c))
(assert (=> b (not c)))
(check-sat)