; COMMAND-LINE:  --solve-bv-as-int=bv
; COMMAND-LINE:  --solve-bv-as-int=sum
; COMMAND-LINE:  --solve-bv-as-int=sum --bv-to-int-use-pow2
; COMMAND-LINE:  --solve-bv-as-int=iand --iand-mode=sum
; COMMAND-LINE:  --solve-bv-as-int=iand --iand-mode=bitwise
; COMMAND-LINE:  --solve-bv-as-int=iand --iand-mode=value
; EXPECT: unsat
(set-logic ALL)
(declare-fun t () (_ BitVec 4))
(declare-fun s () (_ BitVec 4))
(assert (bvult (_ bv8 4) (bvadd (_ bv8 4) (bvlshr t s))))
(assert (forall ((x (_ BitVec 4))) (bvule (bvadd (_ bv8 4) (bvlshr x s)) (_ bv8 4))))
(check-sat)
(exit)
