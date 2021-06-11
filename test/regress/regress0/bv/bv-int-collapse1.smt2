; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () (_ BitVec 16))
(assert (not (= t ((_ int2bv 16) (bv2nat t)))))
(check-sat)
