; COMMAND-LINE: --decision=justification
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unknown)
(set-logic QF_AUFLIA)
(declare-fun REGFILE_INIT () (Array Int Int))
(declare-fun BDEST_S2M_INIT () Int)
(declare-fun CLOCK_INIT () Bool)
(check-sat-assuming ( (let ((_let_0 (ite CLOCK_INIT 1 0))) (let ((_let_1 (ite (ite (= 0 BDEST_S2M_INIT) false true) (store REGFILE_INIT BDEST_S2M_INIT 0) REGFILE_INIT))) (let ((_let_2 (ite (ite CLOCK_INIT false true) (store _let_1 1 0) _let_1))) (not (= (select REGFILE_INIT 0) (select (ite (ite (= 0 (ite (= 1 (ite (= 0 _let_0) 0 1)) 0 (select _let_1 _let_0))) false true) _let_2 (store _let_2 1 0)) 0)))))) ))
