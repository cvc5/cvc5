; COMMAND-LINE: --decision=justification
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unknown)
(set-logic QF_AUFLIA)
(declare-fun REGFILE_INIT () (Array Int Int))
(declare-fun BDEST_S2E_INIT () Int)
(declare-fun IMEM_INIT () (Array Int Int))
(declare-fun OPCODE_OF (Int) Int)
(check-sat-assuming ( (let ((_let_0 (select IMEM_INIT 0))) (let ((_let_1 (OPCODE_OF _let_0))) (let ((_let_2 (ite (ite (= BDEST_S2E_INIT 0) false true) (store REGFILE_INIT BDEST_S2E_INIT 0) REGFILE_INIT))) (let ((_let_3 (ite (ite (= 0 _let_0) false true) (store _let_2 _let_0 0) _let_2))) (not (= (select REGFILE_INIT 0) (select (ite (= _let_1 1) _let_3 (ite (= 0 _let_1) _let_2 (ite (= 16 _let_1) _let_3 _let_2))) 0))))))) ))
