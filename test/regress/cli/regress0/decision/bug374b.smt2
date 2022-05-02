; COMMAND-LINE: --decision=justification --no-unconstrained
; EXPECT: unsat

(set-logic QF_ALL)
(declare-fun _substvar_245_ () Bool)
(declare-fun _substvar_246_ () Bool)
(declare-fun _substvar_247_ () Bool)
(declare-fun group_size_x () (_ BitVec 32))
(declare-fun group_id_x$2 () (_ BitVec 32))
(declare-fun local_id_x$2 () (_ BitVec 32))
(assert (= _substvar_245_ _substvar_246_))
(assert
    (and (bvsge group_id_x$2 #x00000000) (bvsge local_id_x$2 #x00000000) (bvslt local_id_x$2 group_size_x)
         (or (not (bvsgt group_size_x #x00000000)) (not (and (=> _substvar_247_ (bvsge group_id_x$2 #x00000000)) (= _substvar_245_ _substvar_246_))))
    )
  )
(check-sat)
