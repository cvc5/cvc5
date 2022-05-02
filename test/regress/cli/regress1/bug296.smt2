; EXPECT: unsat
(set-logic QF_ALL)
(set-info :status unsat)
(declare-datatypes
  ((MsgResult 0) (MsgTree 0) (TreeResult 0) (MsgTree_Node_recd 0)) (
    ((MsgResult_MsgOK (destMsgResult_MsgOK Real))
      (MsgResult_MsgAudit (destMsgResult_MsgAudit Real)))
    ((MsgTree_Leaf)
      (MsgTree_Node (destMsgTree_Node MsgTree_Node_recd)))
    ((TreeResult_TreeOK (destTreeResult_TreeOK MsgTree))
      (TreeResult_TreeAudit (destTreeResult_TreeAudit Real)))
    ((MsgTree_Node_recd (MsgTree_Node_recd_Value Real)
        (MsgTree_Node_recd_Left MsgTree)
        (MsgTree_Node_recd_Right MsgTree)))))
(declare-fun Guardfn (MsgTree) TreeResult)
(declare-fun Input () MsgTree)
(declare-fun M () Real)
(declare-fun f (Real) MsgResult)
(declare-fun n () MsgTree_Node_recd)
(declare-fun ARB () Bool)
(declare-fun Guard_Checkfn (MsgTree) Bool)
(define-fun DWS_Idempotentfn ((M1 Real)) Bool
  (ite ((_ is MsgResult_MsgOK) (f M1))
    (and ((_ is MsgResult_MsgOK) (f (destMsgResult_MsgOK (f M1))))
      (= (destMsgResult_MsgOK (f M1))
        (destMsgResult_MsgOK (f (destMsgResult_MsgOK (f M1))))))
    (or ((_ is MsgResult_MsgAudit) (f M1)) ARB)))
(assert
  (and
    (=>
      (and (not ((_ is MsgTree_Leaf) Input))
        (and ((_ is MsgTree_Node) Input)
          (and
            (not
              ((_ is MsgResult_MsgAudit)
                (f
                  (MsgTree_Node_recd_Value (destMsgTree_Node Input)))))
            (and
              ((_ is MsgResult_MsgOK)
                (f
                  (MsgTree_Node_recd_Value (destMsgTree_Node Input))))
              (and
                (not
                  ((_ is TreeResult_TreeAudit)
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))))
                (and
                  ((_ is TreeResult_TreeOK)
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input))))
                  ((_ is TreeResult_TreeOK)
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input))))))))))
      (Guard_Checkfn
        (destTreeResult_TreeOK
          (Guardfn
            (MsgTree_Node_recd_Right (destMsgTree_Node Input))))))
    (and
      (=>
        (and (not ((_ is MsgTree_Leaf) Input))
          (and ((_ is MsgTree_Node) Input)
            (and
              (not
                ((_ is MsgResult_MsgAudit)
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input)))))
              (and
                ((_ is MsgResult_MsgOK)
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input))))
                ((_ is TreeResult_TreeOK)
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))))
        (Guard_Checkfn
          (destTreeResult_TreeOK
            (Guardfn
              (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))
      (and
        (DWS_Idempotentfn
          (MsgTree_Node_recd_Value (destMsgTree_Node Input)))
        (and
          ((_ is TreeResult_TreeOK)
            (ite ((_ is MsgTree_Leaf) Input)
              (TreeResult_TreeOK MsgTree_Leaf)
              (ite
                ((_ is MsgResult_MsgAudit)
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input))))
                (TreeResult_TreeAudit
                  (destMsgResult_MsgAudit
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input)))))
                (ite
                  ((_ is TreeResult_TreeAudit)
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input))))
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input)))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input)))
                    (TreeResult_TreeOK
                      (MsgTree_Node
                        (MsgTree_Node_recd
                          (destMsgResult_MsgOK
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input))))))))))))
          (not
            (Guard_Checkfn
              (destTreeResult_TreeOK
                (ite ((_ is MsgTree_Leaf) Input)
                  (TreeResult_TreeOK MsgTree_Leaf)
                  (ite
                    ((_ is MsgResult_MsgAudit)
                      (f
                        (MsgTree_Node_recd_Value
                          (destMsgTree_Node Input))))
                    (TreeResult_TreeAudit
                      (destMsgResult_MsgAudit
                        (f
                          (MsgTree_Node_recd_Value
                            (destMsgTree_Node Input)))))
                    (ite
                      ((_ is TreeResult_TreeAudit)
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input))))
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input)))
                      (ite
                        ((_ is TreeResult_TreeAudit)
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input))))
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))
                        (TreeResult_TreeOK
                          (MsgTree_Node
                            (MsgTree_Node_recd
                              (destMsgResult_MsgOK
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input))))
                              (destTreeResult_TreeOK
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input))))
                              (destTreeResult_TreeOK
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input)))))))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (destTreeResult_TreeOK
        (Guardfn (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))
    (ite
      ((_ is MsgTree_Leaf)
        (destTreeResult_TreeOK
          (Guardfn
            (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (Guardfn
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node Input))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (Guardfn
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node Input))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input)))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input)))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input)))))))))))))
(assert
  (=
    (Guard_Checkfn
      (destTreeResult_TreeOK
        (Guardfn (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))
    (ite
      ((_ is MsgTree_Leaf)
        (destTreeResult_TreeOK
          (Guardfn
            (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input)))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))))))))))))
(assert
  (=
    (Guard_Checkfn
      (destTreeResult_TreeOK
        (ite ((_ is MsgTree_Leaf) Input)
          (TreeResult_TreeOK MsgTree_Leaf)
          (ite
            ((_ is MsgResult_MsgAudit)
              (f (MsgTree_Node_recd_Value (destMsgTree_Node Input))))
            (TreeResult_TreeAudit
              (destMsgResult_MsgAudit
                (f
                  (MsgTree_Node_recd_Value (destMsgTree_Node Input)))))
            (ite
              ((_ is TreeResult_TreeAudit)
                (Guardfn
                  (MsgTree_Node_recd_Left (destMsgTree_Node Input))))
              (Guardfn
                (MsgTree_Node_recd_Left (destMsgTree_Node Input)))
              (ite
                ((_ is TreeResult_TreeAudit)
                  (Guardfn
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node Input))))
                (Guardfn
                  (MsgTree_Node_recd_Right (destMsgTree_Node Input)))
                (TreeResult_TreeOK
                  (MsgTree_Node
                    (MsgTree_Node_recd
                      (destMsgResult_MsgOK
                        (f
                          (MsgTree_Node_recd_Value
                            (destMsgTree_Node Input))))
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input))))
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))))))))))))
    (ite
      ((_ is MsgTree_Leaf)
        (destTreeResult_TreeOK
          (ite ((_ is MsgTree_Leaf) Input)
            (TreeResult_TreeOK MsgTree_Leaf)
            (ite
              ((_ is MsgResult_MsgAudit)
                (f
                  (MsgTree_Node_recd_Value (destMsgTree_Node Input))))
              (TreeResult_TreeAudit
                (destMsgResult_MsgAudit
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input)))))
              (ite
                ((_ is TreeResult_TreeAudit)
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input))))
                (Guardfn
                  (MsgTree_Node_recd_Left (destMsgTree_Node Input)))
                (ite
                  ((_ is TreeResult_TreeAudit)
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input))))
                  (Guardfn
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node Input)))
                  (TreeResult_TreeOK
                    (MsgTree_Node
                      (MsgTree_Node_recd
                        (destMsgResult_MsgOK
                          (f
                            (MsgTree_Node_recd_Value
                              (destMsgTree_Node Input))))
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input))))
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input)))))))))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (ite ((_ is MsgTree_Leaf) Input)
                    (TreeResult_TreeOK MsgTree_Leaf)
                    (ite
                      ((_ is MsgResult_MsgAudit)
                        (f
                          (MsgTree_Node_recd_Value
                            (destMsgTree_Node Input))))
                      (TreeResult_TreeAudit
                        (destMsgResult_MsgAudit
                          (f
                            (MsgTree_Node_recd_Value
                              (destMsgTree_Node Input)))))
                      (ite
                        ((_ is TreeResult_TreeAudit)
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input))))
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))
                        (ite
                          ((_ is TreeResult_TreeAudit)
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input))))
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input)))
                          (TreeResult_TreeOK
                            (MsgTree_Node
                              (MsgTree_Node_recd
                                (destMsgResult_MsgOK
                                  (f
                                    (MsgTree_Node_recd_Value
                                      (destMsgTree_Node Input))))
                                (destTreeResult_TreeOK
                                  (Guardfn
                                    (MsgTree_Node_recd_Left
                                      (destMsgTree_Node Input))))
                                (destTreeResult_TreeOK
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))))))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (destTreeResult_TreeOK
                  (ite ((_ is MsgTree_Leaf) Input)
                    (TreeResult_TreeOK MsgTree_Leaf)
                    (ite
                      ((_ is MsgResult_MsgAudit)
                        (f
                          (MsgTree_Node_recd_Value
                            (destMsgTree_Node Input))))
                      (TreeResult_TreeAudit
                        (destMsgResult_MsgAudit
                          (f
                            (MsgTree_Node_recd_Value
                              (destMsgTree_Node Input)))))
                      (ite
                        ((_ is TreeResult_TreeAudit)
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input))))
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))
                        (ite
                          ((_ is TreeResult_TreeAudit)
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input))))
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input)))
                          (TreeResult_TreeOK
                            (MsgTree_Node
                              (MsgTree_Node_recd
                                (destMsgResult_MsgOK
                                  (f
                                    (MsgTree_Node_recd_Value
                                      (destMsgTree_Node Input))))
                                (destTreeResult_TreeOK
                                  (Guardfn
                                    (MsgTree_Node_recd_Left
                                      (destMsgTree_Node Input))))
                                (destTreeResult_TreeOK
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))))))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (ite ((_ is MsgTree_Leaf) Input)
                        (TreeResult_TreeOK MsgTree_Leaf)
                        (ite
                          ((_ is MsgResult_MsgAudit)
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (TreeResult_TreeAudit
                            (destMsgResult_MsgAudit
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input)))))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input)))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))
                              (TreeResult_TreeOK
                                (MsgTree_Node
                                  (MsgTree_Node_recd
                                    (destMsgResult_MsgOK
                                      (f
                                        (MsgTree_Node_recd_Value
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Left
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Right
                                          (destMsgTree_Node Input)))))))))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (ite ((_ is MsgTree_Leaf) Input)
                      (TreeResult_TreeOK MsgTree_Leaf)
                      (ite
                        ((_ is MsgResult_MsgAudit)
                          (f
                            (MsgTree_Node_recd_Value
                              (destMsgTree_Node Input))))
                        (TreeResult_TreeAudit
                          (destMsgResult_MsgAudit
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input)))))
                        (ite
                          ((_ is TreeResult_TreeAudit)
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input))))
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input)))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input)))
                            (TreeResult_TreeOK
                              (MsgTree_Node
                                (MsgTree_Node_recd
                                  (destMsgResult_MsgOK
                                    (f
                                      (MsgTree_Node_recd_Value
                                        (destMsgTree_Node Input))))
                                  (destTreeResult_TreeOK
                                    (Guardfn
                                      (MsgTree_Node_recd_Left
                                        (destMsgTree_Node Input))))
                                  (destTreeResult_TreeOK
                                    (Guardfn
                                      (MsgTree_Node_recd_Right
                                        (destMsgTree_Node Input)))))))))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (destTreeResult_TreeOK
                    (ite ((_ is MsgTree_Leaf) Input)
                      (TreeResult_TreeOK MsgTree_Leaf)
                      (ite
                        ((_ is MsgResult_MsgAudit)
                          (f
                            (MsgTree_Node_recd_Value
                              (destMsgTree_Node Input))))
                        (TreeResult_TreeAudit
                          (destMsgResult_MsgAudit
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input)))))
                        (ite
                          ((_ is TreeResult_TreeAudit)
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input))))
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input)))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input)))
                            (TreeResult_TreeOK
                              (MsgTree_Node
                                (MsgTree_Node_recd
                                  (destMsgResult_MsgOK
                                    (f
                                      (MsgTree_Node_recd_Value
                                        (destMsgTree_Node Input))))
                                  (destTreeResult_TreeOK
                                    (Guardfn
                                      (MsgTree_Node_recd_Left
                                        (destMsgTree_Node Input))))
                                  (destTreeResult_TreeOK
                                    (Guardfn
                                      (MsgTree_Node_recd_Right
                                        (destMsgTree_Node Input)))))))))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Left
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (Guardfn
              (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Left
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input)))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Right
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (Guardfn
              (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Right (destMsgTree_Node Input)))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Right
                              (destMsgTree_Node Input)))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input)))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Left
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (Guardfn
              (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Left
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input)))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Right
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (Guardfn
              (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Left (destMsgTree_Node Input)))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (Guardfn
                            (MsgTree_Node_recd_Left
                              (destMsgTree_Node Input)))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (Guardfn
                          (MsgTree_Node_recd_Left
                            (destMsgTree_Node Input)))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Left
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (ite ((_ is MsgTree_Leaf) Input)
              (TreeResult_TreeOK MsgTree_Leaf)
              (ite
                ((_ is MsgResult_MsgAudit)
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input))))
                (TreeResult_TreeAudit
                  (destMsgResult_MsgAudit
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input)))))
                (ite
                  ((_ is TreeResult_TreeAudit)
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input))))
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input)))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input)))
                    (TreeResult_TreeOK
                      (MsgTree_Node
                        (MsgTree_Node_recd
                          (destMsgResult_MsgOK
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input)))))))))))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (ite ((_ is MsgTree_Leaf) Input)
                (TreeResult_TreeOK MsgTree_Leaf)
                (ite
                  ((_ is MsgResult_MsgAudit)
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input))))
                  (TreeResult_TreeAudit
                    (destMsgResult_MsgAudit
                      (f
                        (MsgTree_Node_recd_Value
                          (destMsgTree_Node Input)))))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))
                    (ite
                      ((_ is TreeResult_TreeAudit)
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input))))
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input)))
                      (TreeResult_TreeOK
                        (MsgTree_Node
                          (MsgTree_Node_recd
                            (destMsgResult_MsgOK
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))))))))))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (ite ((_ is MsgTree_Leaf) Input)
                        (TreeResult_TreeOK MsgTree_Leaf)
                        (ite
                          ((_ is MsgResult_MsgAudit)
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (TreeResult_TreeAudit
                            (destMsgResult_MsgAudit
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input)))))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input)))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))
                              (TreeResult_TreeOK
                                (MsgTree_Node
                                  (MsgTree_Node_recd
                                    (destMsgResult_MsgOK
                                      (f
                                        (MsgTree_Node_recd_Value
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Left
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Right
                                          (destMsgTree_Node Input))))))))))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Left
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (ite ((_ is MsgTree_Leaf) Input)
                        (TreeResult_TreeOK MsgTree_Leaf)
                        (ite
                          ((_ is MsgResult_MsgAudit)
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (TreeResult_TreeAudit
                            (destMsgResult_MsgAudit
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input)))))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input)))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))
                              (TreeResult_TreeOK
                                (MsgTree_Node
                                  (MsgTree_Node_recd
                                    (destMsgResult_MsgOK
                                      (f
                                        (MsgTree_Node_recd_Value
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Left
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Right
                                          (destMsgTree_Node Input))))))))))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Left
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (ite ((_ is MsgTree_Leaf) Input)
                            (TreeResult_TreeOK MsgTree_Leaf)
                            (ite
                              ((_ is MsgResult_MsgAudit)
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input))))
                              (TreeResult_TreeAudit
                                (destMsgResult_MsgAudit
                                  (f
                                    (MsgTree_Node_recd_Value
                                      (destMsgTree_Node Input)))))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Left
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input)))
                                (ite
                                  ((_ is TreeResult_TreeAudit)
                                    (Guardfn
                                      (MsgTree_Node_recd_Right
                                        (destMsgTree_Node Input))))
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input)))
                                  (TreeResult_TreeOK
                                    (MsgTree_Node
                                      (MsgTree_Node_recd
                                        (destMsgResult_MsgOK
                                          (f
                                            (MsgTree_Node_recd_Value
                                              (destMsgTree_Node Input))))
                                        (destTreeResult_TreeOK
                                          (Guardfn
                                            (MsgTree_Node_recd_Left
                                              (destMsgTree_Node Input))))
                                        (destTreeResult_TreeOK
                                          (Guardfn
                                            (MsgTree_Node_recd_Right
                                              (destMsgTree_Node Input)))))))))))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (ite ((_ is MsgTree_Leaf) Input)
                          (TreeResult_TreeOK MsgTree_Leaf)
                          (ite
                            ((_ is MsgResult_MsgAudit)
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (TreeResult_TreeAudit
                              (destMsgResult_MsgAudit
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input)))))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input)))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input)))
                                (TreeResult_TreeOK
                                  (MsgTree_Node
                                    (MsgTree_Node_recd
                                      (destMsgResult_MsgOK
                                        (f
                                          (MsgTree_Node_recd_Value
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Left
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Right
                                            (destMsgTree_Node Input)))))))))))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Left
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (ite ((_ is MsgTree_Leaf) Input)
                          (TreeResult_TreeOK MsgTree_Leaf)
                          (ite
                            ((_ is MsgResult_MsgAudit)
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (TreeResult_TreeAudit
                              (destMsgResult_MsgAudit
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input)))))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input)))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input)))
                                (TreeResult_TreeOK
                                  (MsgTree_Node
                                    (MsgTree_Node_recd
                                      (destMsgResult_MsgOK
                                        (f
                                          (MsgTree_Node_recd_Value
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Left
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Right
                                            (destMsgTree_Node Input)))))))))))))))))))))))
(assert
  (=
    (Guard_Checkfn
      (MsgTree_Node_recd_Right
        (destMsgTree_Node
          (destTreeResult_TreeOK
            (ite ((_ is MsgTree_Leaf) Input)
              (TreeResult_TreeOK MsgTree_Leaf)
              (ite
                ((_ is MsgResult_MsgAudit)
                  (f
                    (MsgTree_Node_recd_Value
                      (destMsgTree_Node Input))))
                (TreeResult_TreeAudit
                  (destMsgResult_MsgAudit
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input)))))
                (ite
                  ((_ is TreeResult_TreeAudit)
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input))))
                  (Guardfn
                    (MsgTree_Node_recd_Left (destMsgTree_Node Input)))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Right
                        (destMsgTree_Node Input)))
                    (TreeResult_TreeOK
                      (MsgTree_Node
                        (MsgTree_Node_recd
                          (destMsgResult_MsgOK
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input))))
                          (destTreeResult_TreeOK
                            (Guardfn
                              (MsgTree_Node_recd_Right
                                (destMsgTree_Node Input)))))))))))))))
    (ite
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (ite ((_ is MsgTree_Leaf) Input)
                (TreeResult_TreeOK MsgTree_Leaf)
                (ite
                  ((_ is MsgResult_MsgAudit)
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input))))
                  (TreeResult_TreeAudit
                    (destMsgResult_MsgAudit
                      (f
                        (MsgTree_Node_recd_Value
                          (destMsgTree_Node Input)))))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))
                    (ite
                      ((_ is TreeResult_TreeAudit)
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input))))
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input)))
                      (TreeResult_TreeOK
                        (MsgTree_Node
                          (MsgTree_Node_recd
                            (destMsgResult_MsgOK
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))))))))))))))
      true
      (and
        ((_ is MsgResult_MsgOK)
          (f
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (ite ((_ is MsgTree_Leaf) Input)
                        (TreeResult_TreeOK MsgTree_Leaf)
                        (ite
                          ((_ is MsgResult_MsgAudit)
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (TreeResult_TreeAudit
                            (destMsgResult_MsgAudit
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input)))))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input)))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))
                              (TreeResult_TreeOK
                                (MsgTree_Node
                                  (MsgTree_Node_recd
                                    (destMsgResult_MsgOK
                                      (f
                                        (MsgTree_Node_recd_Value
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Left
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Right
                                          (destMsgTree_Node Input))))))))))))))))))
        (and
          (=
            (MsgTree_Node_recd_Value
              (destMsgTree_Node
                (MsgTree_Node_recd_Right
                  (destMsgTree_Node
                    (destTreeResult_TreeOK
                      (ite ((_ is MsgTree_Leaf) Input)
                        (TreeResult_TreeOK MsgTree_Leaf)
                        (ite
                          ((_ is MsgResult_MsgAudit)
                            (f
                              (MsgTree_Node_recd_Value
                                (destMsgTree_Node Input))))
                          (TreeResult_TreeAudit
                            (destMsgResult_MsgAudit
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input)))))
                          (ite
                            ((_ is TreeResult_TreeAudit)
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (Guardfn
                              (MsgTree_Node_recd_Left
                                (destMsgTree_Node Input)))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input)))
                              (TreeResult_TreeOK
                                (MsgTree_Node
                                  (MsgTree_Node_recd
                                    (destMsgResult_MsgOK
                                      (f
                                        (MsgTree_Node_recd_Value
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Left
                                          (destMsgTree_Node Input))))
                                    (destTreeResult_TreeOK
                                      (Guardfn
                                        (MsgTree_Node_recd_Right
                                          (destMsgTree_Node Input))))))))))))))))
            (destMsgResult_MsgOK
              (f
                (MsgTree_Node_recd_Value
                  (destMsgTree_Node
                    (MsgTree_Node_recd_Right
                      (destMsgTree_Node
                        (destTreeResult_TreeOK
                          (ite ((_ is MsgTree_Leaf) Input)
                            (TreeResult_TreeOK MsgTree_Leaf)
                            (ite
                              ((_ is MsgResult_MsgAudit)
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input))))
                              (TreeResult_TreeAudit
                                (destMsgResult_MsgAudit
                                  (f
                                    (MsgTree_Node_recd_Value
                                      (destMsgTree_Node Input)))))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Left
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input)))
                                (ite
                                  ((_ is TreeResult_TreeAudit)
                                    (Guardfn
                                      (MsgTree_Node_recd_Right
                                        (destMsgTree_Node Input))))
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input)))
                                  (TreeResult_TreeOK
                                    (MsgTree_Node
                                      (MsgTree_Node_recd
                                        (destMsgResult_MsgOK
                                          (f
                                            (MsgTree_Node_recd_Value
                                              (destMsgTree_Node Input))))
                                        (destTreeResult_TreeOK
                                          (Guardfn
                                            (MsgTree_Node_recd_Left
                                              (destMsgTree_Node Input))))
                                        (destTreeResult_TreeOK
                                          (Guardfn
                                            (MsgTree_Node_recd_Right
                                              (destMsgTree_Node Input)))))))))))))))))))
          (and
            (Guard_Checkfn
              (MsgTree_Node_recd_Left
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (ite ((_ is MsgTree_Leaf) Input)
                          (TreeResult_TreeOK MsgTree_Leaf)
                          (ite
                            ((_ is MsgResult_MsgAudit)
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (TreeResult_TreeAudit
                              (destMsgResult_MsgAudit
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input)))))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input)))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input)))
                                (TreeResult_TreeOK
                                  (MsgTree_Node
                                    (MsgTree_Node_recd
                                      (destMsgResult_MsgOK
                                        (f
                                          (MsgTree_Node_recd_Value
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Left
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Right
                                            (destMsgTree_Node Input)))))))))))))))))
            (Guard_Checkfn
              (MsgTree_Node_recd_Right
                (destMsgTree_Node
                  (MsgTree_Node_recd_Right
                    (destMsgTree_Node
                      (destTreeResult_TreeOK
                        (ite ((_ is MsgTree_Leaf) Input)
                          (TreeResult_TreeOK MsgTree_Leaf)
                          (ite
                            ((_ is MsgResult_MsgAudit)
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (TreeResult_TreeAudit
                              (destMsgResult_MsgAudit
                                (f
                                  (MsgTree_Node_recd_Value
                                    (destMsgTree_Node Input)))))
                            (ite
                              ((_ is TreeResult_TreeAudit)
                                (Guardfn
                                  (MsgTree_Node_recd_Left
                                    (destMsgTree_Node Input))))
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input)))
                              (ite
                                ((_ is TreeResult_TreeAudit)
                                  (Guardfn
                                    (MsgTree_Node_recd_Right
                                      (destMsgTree_Node Input))))
                                (Guardfn
                                  (MsgTree_Node_recd_Right
                                    (destMsgTree_Node Input)))
                                (TreeResult_TreeOK
                                  (MsgTree_Node
                                    (MsgTree_Node_recd
                                      (destMsgResult_MsgOK
                                        (f
                                          (MsgTree_Node_recd_Value
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Left
                                            (destMsgTree_Node Input))))
                                      (destTreeResult_TreeOK
                                        (Guardfn
                                          (MsgTree_Node_recd_Right
                                            (destMsgTree_Node Input)))))))))))))))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Right (destMsgTree_Node Input))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Right (destMsgTree_Node Input))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (Guardfn
                (MsgTree_Node_recd_Left (destMsgTree_Node Input))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Left
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (ite ((_ is MsgTree_Leaf) Input)
                (TreeResult_TreeOK MsgTree_Leaf)
                (ite
                  ((_ is MsgResult_MsgAudit)
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input))))
                  (TreeResult_TreeAudit
                    (destMsgResult_MsgAudit
                      (f
                        (MsgTree_Node_recd_Value
                          (destMsgTree_Node Input)))))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))
                    (ite
                      ((_ is TreeResult_TreeAudit)
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input))))
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input)))
                      (TreeResult_TreeOK
                        (MsgTree_Node
                          (MsgTree_Node_recd
                            (destMsgResult_MsgOK
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input))))))))))))))))))
(assert
  (not
    (not
      ((_ is MsgTree_Leaf)
        (MsgTree_Node_recd_Right
          (destMsgTree_Node
            (destTreeResult_TreeOK
              (ite ((_ is MsgTree_Leaf) Input)
                (TreeResult_TreeOK MsgTree_Leaf)
                (ite
                  ((_ is MsgResult_MsgAudit)
                    (f
                      (MsgTree_Node_recd_Value
                        (destMsgTree_Node Input))))
                  (TreeResult_TreeAudit
                    (destMsgResult_MsgAudit
                      (f
                        (MsgTree_Node_recd_Value
                          (destMsgTree_Node Input)))))
                  (ite
                    ((_ is TreeResult_TreeAudit)
                      (Guardfn
                        (MsgTree_Node_recd_Left
                          (destMsgTree_Node Input))))
                    (Guardfn
                      (MsgTree_Node_recd_Left
                        (destMsgTree_Node Input)))
                    (ite
                      ((_ is TreeResult_TreeAudit)
                        (Guardfn
                          (MsgTree_Node_recd_Right
                            (destMsgTree_Node Input))))
                      (Guardfn
                        (MsgTree_Node_recd_Right
                          (destMsgTree_Node Input)))
                      (TreeResult_TreeOK
                        (MsgTree_Node
                          (MsgTree_Node_recd
                            (destMsgResult_MsgOK
                              (f
                                (MsgTree_Node_recd_Value
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Left
                                  (destMsgTree_Node Input))))
                            (destTreeResult_TreeOK
                              (Guardfn
                                (MsgTree_Node_recd_Right
                                  (destMsgTree_Node Input))))))))))))))))))
(check-sat)
(exit)
