; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores --no-check-proofs 
; EXPECT: sat
(set-logic QF_UFBVNIRA)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))

(declare-fun n () Int)
(declare-fun r () Real)

(declare-fun f (Int Real)  (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) Int)

(assert (= (f n r) x))
(assert (= (g y) n))

(check-sat)
