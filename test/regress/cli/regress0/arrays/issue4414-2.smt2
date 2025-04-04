; COMMAND-LINE: --arrays-exp
; EXPECT: sat
(set-option :check-models true)
(set-option :check-unsat-cores true)
(set-logic QF_ALIA)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(declare-const c (Array Int Int))
(assert (= c ((as const (Array Int Int)) 0)))
(assert (= a (select c b)))
(check-sat)
