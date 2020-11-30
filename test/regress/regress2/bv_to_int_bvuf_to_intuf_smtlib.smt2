;COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1 --no-produce-unsat-cores
;EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun z$n0s32 () (_ BitVec 32))
(declare-fun dataOut () (_ BitVec 32))
(declare-fun z$2 () (_ BitVec 1))
(declare-fun stageOne () (_ BitVec 32))
(declare-fun z$4 () (_ BitVec 1))
(declare-fun stageTwo () (_ BitVec 32))
(declare-fun z$6 () (_ BitVec 1))
(declare-fun tmp_stageOne () (_ BitVec 32))
(declare-fun z$8 () (_ BitVec 1))
(declare-fun tmp_stageTwo () (_ BitVec 32))
(declare-fun z$10 () (_ BitVec 1))
(declare-fun reset_ () (_ BitVec 1))
(declare-fun z$14 () (_ BitVec 1))
(declare-fun Add_32_32_32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun z$15 () (_ BitVec 32))
(declare-fun z$17 () (_ BitVec 32))
(declare-fun dataOut$next () (_ BitVec 32))
(declare-fun z$19 () (_ BitVec 1))
(declare-fun c1 () (_ BitVec 32))
(declare-fun dataIn () (_ BitVec 32))
(declare-fun z$23 () (_ BitVec 32))
(declare-fun stageOne$next () (_ BitVec 32))
(declare-fun z$25 () (_ BitVec 1))
(declare-fun c2 () (_ BitVec 32))
(declare-fun z$28 () (_ BitVec 32))
(declare-fun stageTwo$next () (_ BitVec 32))
(declare-fun z$30 () (_ BitVec 1))
(declare-fun tmp_stageOne$next () (_ BitVec 32))
(declare-fun z$32 () (_ BitVec 1))
(declare-fun tmp_stageTwo$next () (_ BitVec 32))
(declare-fun z$34 () (_ BitVec 1))
(declare-fun z$35 () (_ BitVec 1))
(declare-fun z$55 () (_ BitVec 32))
(declare-fun z$57 () (_ BitVec 1))
(declare-fun z$58 () (_ BitVec 1))
(declare-fun z$59 () (_ BitVec 1))
(declare-fun prop$next () (_ BitVec 1))
(declare-fun z$61 () (_ BitVec 1))
(declare-fun z$54 () (_ BitVec 1))
(declare-fun z$63 () (_ BitVec 1))
(assert
 (= z$15 (Add_32_32_32 stageTwo stageOne)))
(assert
 (= z$17 (ite (= z$14 (_ bv1 1)) z$15 z$n0s32)))
(assert
 (= z$19 (ite (= dataOut$next z$17) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$25 (ite (= stageOne$next z$23) (_ bv1 1) (_ bv0 1))))

 
(assert
 (= z$32 (ite (= tmp_stageOne$next stageOne) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$34 (ite (= tmp_stageTwo$next stageTwo) (_ bv1 1) (_ bv0 1))))
(assert
 (let (($x130 (and (= z$19 (_ bv1 1)) (= z$25 (_ bv1 1)) (= z$30 (_ bv1 1)) (= z$32 (_ bv1 1)) (= z$34 (_ bv1 1)))))
 (= z$35 (ite $x130 (_ bv1 1) (_ bv0 1)))))
(assert
 (= z$55 (Add_32_32_32 tmp_stageTwo$next tmp_stageOne$next)))
(assert
 (= z$57 (ite (= dataOut$next z$55) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$58 (ite (= dataOut$next z$n0s32) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$59 (ite (or (= z$57 (_ bv1 1)) (= z$58 (_ bv1 1))) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$61 (ite (= prop$next z$59) (_ bv1 1) (_ bv0 1))))
(assert
 (= z$54 (ite (= prop$next (_ bv0 1)) (_ bv1 1) (_ bv0 1))))
(assert
 (let (($x52 (= z$2 (_ bv1 1))))
 (let (($x165 (and $x52 (= z$4 (_ bv1 1)) (= z$6 (_ bv1 1)) (= z$8 (_ bv1 1)) (= z$10 (_ bv1 1)) (= z$35 (_ bv1 1)) (= z$61 (_ bv1 1)) (= z$54 (_ bv1 1)))))
 (= z$63 (ite $x165 (_ bv1 1) (_ bv0 1))))))
(assert
 (= z$63 (_ bv1 1)))
(check-sat)
(exit)
