; COMMAND-LINE:  --solve-bv-as-int=sum -q
; COMMAND-LINE:  --solve-bv-as-int=sum  --bv-to-int-use-pow2 -q
; EXPECT: sat
(set-logic BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(assert (not (and (=> (bvsge (_ bv0 3) t) (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t))) (=> (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t)) (bvsge (_ bv0 3) t)))))
(check-sat)
(exit)
