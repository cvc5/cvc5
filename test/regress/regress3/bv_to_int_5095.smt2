; COMMAND: --solve-bv-as-int=sum --incremental
; EXPECT: sat
(set-logic QF_BV)
(declare-fun _substvar_27_ () Bool)
(declare-const bv_40-3 (_ BitVec 40))
(assert (= bv_40-3 (_ bv0 40)))
(push 1)
(assert _substvar_27_)
(check-sat)