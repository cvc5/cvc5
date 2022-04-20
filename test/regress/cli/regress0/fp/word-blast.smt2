; DISABLE-TESTER: lfsc
; COMMAND-LINE: --fp-lazy-wb
; EXPECT: unsat
(set-logic QF_BVFP)
(declare-fun meters_ackermann!0 () (_ BitVec 64))
(assert
 (let ((?x8 ((_ to_fp 11 53) meters_ackermann!0)))
 (fp.geq ?x8 ((_ to_fp 11 53) (_ bv0 64)))))
(assert
 (let ((?x8 ((_ to_fp 11 53) meters_ackermann!0)))
 (fp.leq ?x8 ((_ to_fp 11 53) (_ bv4652007308841189376 64)))))
(assert
 (let ((?x19 ((_ sign_extend 32) ((_ fp.to_sbv 32) roundTowardZero (fp.abs ((_ to_fp 11 53) meters_ackermann!0))))))
(not (not (bvult (_ bv9223372036854775807 64) ?x19)))))
(check-sat)
(exit)
