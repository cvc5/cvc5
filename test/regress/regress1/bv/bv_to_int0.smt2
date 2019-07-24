; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun _substvar_187_ () (_ BitVec 32))
(assert 
  (let ((?v_4 (bvsub (_ bv233 32) (bvsub _substvar_187_ (_ bv48 32))))) 
  (and 
    (bvsle 
      (bvsub 
        (_ bv513 32) 
        (bvshl 
          ((_ zero_extend 24) 
            (bvxor 
              ((_ extract 15 8) ?v_4) 
              ((_ extract 7 0) ?v_4))) 
          (_ bv24 32))) 
      (_ bv0 32)
    ) 
    (bvslt 
      (bvsub _substvar_187_ (_ bv149 32)) 
      (_ bv0 32)
    ) 
    (bvsle 
      (_ bv0 32) 
      (bvsub _substvar_187_ (_ bv148 32))
    )
  )
  )
)
(check-sat)
(exit)
