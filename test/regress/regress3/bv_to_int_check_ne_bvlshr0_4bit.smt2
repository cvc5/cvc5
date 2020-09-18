; COMMAND-LINE:  --solve-bv-as-int=bv 
(set-logic BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool
(or (distinct t (_ bv0 4)) (bvult s (_ bv4 4)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 4))) (distinct (bvlshr x s) t)))
  (=> (exists ((x (_ BitVec 4))) (distinct (bvlshr x s) t)) (SC s t))
  )
 )
)
(check-sat)
(exit)
