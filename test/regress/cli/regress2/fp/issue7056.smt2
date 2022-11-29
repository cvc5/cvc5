; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; timeout with unsat cores
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(define-fun fp.isFinite32 ((x Float32)) Bool (not (or (fp.isInfinite x) (fp.isNaN x))))
(define-fun fp.isIntegral32 ((x Float32)) Bool (or (fp.isZero x) (and (fp.isNormal x) (= x (fp.roundToIntegral RNE x)))))

(declare-sort t 0)
(declare-const a t)
(declare-fun first (t) Int)
(declare-fun last (t) Int)
(define-fun length ((b t)) Int (ite (<= (first b) (last b)) (+ (- (last b) (first b)) 1) 0))

(define-fun contained ((x Float32)) Bool (and
  (fp.leq x (fp #b0 #b01111111 #b00000000000000000000000))
  (fp.leq (fp #b0 #b00000000 #b00000000000000000000000) x)))


(declare-const i Int)
(declare-const x Float32)
(assert (and (<= (length a) 1000) (< 0 (length a))))
(assert (= i (first a)))
(assert (contained x))
(assert (not (fp.isFinite32 (fp.mul RNE (fp.mul RNE (fp #b0 #b10010010 #b11101000010010000000000) ((_ to_fp 8 24) RNE (to_real (length a))))
                                        x))))
(set-info :status unsat)
(check-sat)
