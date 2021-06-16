(set-logic QF_AUFBV)
(set-option :produce-models true)

(define-sort Index () (_ BitVec 2))
(define-sort Element () (_ BitVec 32))
(define-sort ArraySort () (Array Index Element))

; An array variable
(declare-const fstArray ArraySort)
(declare-const sndArray ArraySort)
(declare-const thirdArray ArraySort)
(declare-const fourthArray ArraySort)
; Making utility bit-vector constants
(define-const zeroI Index (_ bv0 2))
(define-const oneI Index (_ bv1 2))
(define-const twoI Index (_ bv2 2))
(define-const threeI Index (_ bv3 2))

(define-const zeroE Element (_ bv0 32))
(define-const twoE Element (_ bv2 32))

; Asserting that current_array[0] > 0
(assert (bvsgt (select fstArray zeroI) zeroE))

; Building the assertions (negated) in the loop unrolling

; current[0] < current [1]
(assert (not (bvslt (select fstArray zeroI) (bvmul twoE (select fstArray zeroI)))))
; current[1] = 2 * current[0]
(assert (= sndArray (store fstArray oneI (bvmul twoE (select fstArray zeroI)))))

; current[1] < current [2]
(assert (not (bvslt (select sndArray oneI) (bvmul twoE (select sndArray oneI)))))
; current[2] = 2 * current[1]
(assert (= thirdArray (store sndArray twoI (bvmul twoE (select sndArray oneI)))))

; current[2] < current [3]
(assert (not (bvslt (select sndArray twoI) (bvmul twoE (select sndArray twoI)))))
; current[3] = 2 * current[2]
(assert (= fourthArray (store sndArray threeI (bvmul twoE (select sndArray twoI)))))

(check-sat)
(get-value (fourthArray (select fourthArray zeroI)))
