; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((UNIT 0)) (((Unit))))
(declare-datatypes ((BOOL 0)) (((Truth) (Falsity))))

; Decls     --------------
(declare-sort node$type 0)
(declare-sort data$type 0)
(declare-datatypes ((cache_state$type 0)) (((invalid) (shared) (exclusive))))
(declare-datatypes ((cache$type 0)) (((c_cache$type (c_state cache_state$type) (c_data data$type)))))
(declare-datatypes ((msg_cmd$type 0)) (((empty) (reqs) (reqe) (inv) (invack) (gnts) (gnte))))
(declare-datatypes ((msg$type 0)) (((c_msg$type (m_cmd msg_cmd$type) (m_data data$type)))))
(declare-fun dummy () data$type)

; Var Decls --------------
(declare-fun memdata$1 () data$type)
(declare-fun shrset$1 () (Array node$type BOOL))
(declare-fun recv_invack$i () node$type)
(declare-fun exgntd () BOOL)
(declare-fun chan3$1 () (Array node$type msg$type))
(declare-fun shrset () (Array node$type BOOL))
(declare-fun exgntd$1 () BOOL)
(declare-fun chan2 () (Array node$type msg$type))
(declare-fun chan3 () (Array node$type msg$type))
(declare-fun auxnode () node$type)
(declare-fun curcmd () msg_cmd$type)

; Asserts   --------------
(assert (not (=> (and (and (forall ((n node$type))
                                                      (=> (= (m_cmd (select
                                                                    chan2
                                                                    n))
                                                          gnte) (= exgntd
                                                                Truth)))
                                                 (forall ((n node$type))
                                                 (=> (= exgntd Truth)
                                                 (= (select shrset n)
                                                 (ite (= n auxnode) Truth
                                                 Falsity))))) (forall
                                                              ((n node$type))
                                                              (=> (=
                                                                  (m_cmd
                                                                  (select
                                                                  chan3
                                                                  n))
                                                                  invack)
                                                              (= (m_cmd
                                                                 (select
                                                                 chan2
                                                                 n))
                                                              empty))))
                                        (=> (= (m_cmd (select chan3 recv_invack$i))
                                            invack) (=> (not (= curcmd empty))
                                                    (=> (= chan3$1 (store
                                                                   chan3
                                                                   recv_invack$i
                                                                   (let (
                                                                   (vup_228
                                                                   (select
                                                                   chan3
                                                                   recv_invack$i)))
                                                                   (c_msg$type
                                                                   empty
                                                                   (m_data
                                                                   vup_228)))))
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
                                                            (=> (= (m_cmd
                                                                   (select
                                                                   chan2
                                                                   n))
                                                                gnte)
                                                            (= exgntd$1
                                                            Truth)))))
                                                       Truth Falsity)
                                                       (ite (forall (
                                                                    (n node$type))
                                                            (=> (= (m_cmd
                                                                   (select
                                                                   chan2
                                                                   n))
                                                                gnte)
                                                            (= exgntd
                                                            Truth)))
                                                       Truth Falsity))
                                                    Truth))))))))

(check-sat)
(exit)
