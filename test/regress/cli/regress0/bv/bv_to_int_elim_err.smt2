; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; EXPECT: sat
(set-logic QF_BV)
(declare-fun _substvar_183_ () (_ BitVec 32))
(assert (let ((?x15 ((_ sign_extend 0) _substvar_183_))) (bvsle ((_ zero_extend 24) ((_ extract 15 8) (bvadd ?x15 (_ bv4294966758 32)))) (bvadd ?x15 ?x15))))
(check-sat)
(exit)
