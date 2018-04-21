; COMMAND-LINE: --finite-model-find --lang=smt2.5
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-datatypes () ((UNIT (Unit))))
(declare-datatypes () ((BOOL (Truth) (Falsity))))

; Decls     --------------
(declare-sort node$type 0)
(declare-sort data$type 0)
(declare-datatypes () ((cache_state$type (invalid) (shared) (exclusive))))
(declare-datatypes () ((cache$type (c_cache$type (c_state cache_state$type) (c_data data$type)))))
(declare-datatypes () ((msg_cmd$type (empty) (reqs) (reqe) (inv) (invack) (gnts) (gnte))))
(declare-datatypes () ((msg$type (c_msg$type (m_cmd msg_cmd$type) (m_data data$type)))))
(declare-fun dummy () data$type)

; Var Decls --------------
(declare-fun memdata$1 () data$type)
(declare-fun shrset$1 () (Array node$type BOOL))
(declare-fun recv_invack$i () node$type)
(declare-fun exgntd () BOOL)
(declare-fun invset () (Array node$type BOOL))
(declare-fun chan3$1 () (Array node$type msg$type))
(declare-fun shrset () (Array node$type BOOL))
(declare-fun exgntd$1 () BOOL)
(declare-fun chan2 () (Array node$type msg$type))
(declare-fun chan3 () (Array node$type msg$type))
(declare-fun curcmd () msg_cmd$type)

; Asserts   --------------
(assert (not (=> (and (forall ((n node$type)) 
                                                 (=> (= (select invset n) 
                                                     Truth) (= (select 
                                                               shrset 
                                                               n) Truth))) 
                                            (forall ((n node$type)) (=> 
                                                                    (or 
                                                                    (= 
                                                                    (m_cmd 
                                                                    (select 
                                                                    chan2 
                                                                    n)) 
                                                                    inv) 
                                                                    (= 
                                                                    (m_cmd 
                                                                    (select 
                                                                    chan3 
                                                                    n)) 
                                                                    invack)) 
                                                                    (not 
                                                                    (= 
                                                                    (select 
                                                                    invset 
                                                                    n) 
                                                                    Truth))))) 
                                        (=> (= (m_cmd (select chan3 recv_invack$i)) 
                                            invack) (=> (not (= curcmd empty)) 
                                                    (=> (= chan3$1 (store 
                                                                   chan3 
                                                                   recv_invack$i 
                                                                   (let (
                                                                   (vup_101 
                                                                   (select 
                                                                   chan3 
                                                                   recv_invack$i))) 
                                                                   (c_msg$type 
                                                                   empty 
                                                                   (m_data 
                                                                   vup_101))))) 
                                                    (=> (= shrset$1 (store 
                                                                    shrset 
                                                                    recv_invack$i 
                                                                    Falsity)) 
                                                    (= (ite (= exgntd Truth) 
                                                       (ite (=> (= exgntd$1 
                                                                Falsity) 
                                                            (=> (= memdata$1 
                                                                (m_data 
                                                                (select 
                                                                chan3$1 
                                                                recv_invack$i))) 
                                                            (forall (
                                                                    (n node$type)) 
                                                            (=> (= (select 
                                                                   invset 
                                                                   n) 
                                                                Truth) 
                                                            (= (select 
                                                               shrset$1 
                                                               n) Truth))))) 
                                                       Truth Falsity) 
                                                       (ite (forall (
                                                                    (n node$type)) 
                                                            (=> (= (select 
                                                                   invset 
                                                                   n) 
                                                                Truth) 
                                                            (= (select 
                                                               shrset$1 
                                                               n) Truth))) 
                                                       Truth Falsity)) 
                                                    Truth))))))))
                           
(check-sat)
(exit)
