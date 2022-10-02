(set-logic QF_AUFBV)
(set-option :produce-models true)

; Consider the following code (where size is some previously defined constant):


;   Assert (current_array[0] > 0);
;   for (unsigned i = 1; i < k; ++i) {
;     current_array[i] = 2 * current_array[i - 1];
;     Assert (current_array[i-1] < current_array[i]);
;     }

; We want to check whether the assertion in the body of the for loop holds
; throughout the loop. We will do so for k = 4.


(define-sort Index () (_ BitVec 2))
(define-sort Element () (_ BitVec 32))
(define-sort ArraySort () (Array Index Element))

; Declaring the array
(declare-const current_array ArraySort)

; Making utility bit-vector constants
(define-const zeroI Index (_ bv0 2))
(define-const oneI Index (_ bv1 2))
(define-const twoI Index (_ bv2 2))
(define-const threeI Index (_ bv3 2))

(define-const zeroE Element (_ bv0 32))
(define-const twoE Element (_ bv2 32))

; Asserting that current_array[0] > 0
(assert (bvsgt (select current_array zeroI) zeroE))

; Building the formulas representing loop unrolling

; current_array[0] < array [1]
(define-const unroll1 Bool (bvslt (select current_array zeroI) (bvmul twoE (select current_array zeroI))))
; current_array[1] = 2 * current_array[0]
(define-const current_array_ ArraySort (store current_array oneI (bvmul twoE (select current_array zeroI))))

; current_array[1] < array [2]
(define-const unroll2 Bool (bvslt (select current_array_ oneI) (bvmul twoE (select current_array_ oneI))))
; current_array[2] = 2 * current_array[1]
(define-const current_array__ ArraySort (store current_array_ twoI (bvmul twoE (select current_array_ oneI))))

; current_array[2] < array [3]
(define-const unroll3 Bool (bvslt (select current_array_ twoI) (bvmul twoE (select current_array_ twoI))))
; current_array[3] = 2 * current_array[2]
(define-const current_array___ ArraySort (store current_array_ threeI (bvmul twoE (select current_array_ twoI))))

(assert (not (and unroll1 unroll2 unroll3)))

(check-sat)
(get-value (current_array___ (select current_array___ zeroI)))
