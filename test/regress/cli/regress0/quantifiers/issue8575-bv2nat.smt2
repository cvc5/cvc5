; EXPECT: unsat
(set-logic AUFBVFPDTNIRA)
(set-info :smt-lib-version 2.6)

(declare-sort uns32 0)

;; to_rep
(declare-fun to_rep1 (uns32) (_ BitVec 32))

;; lo
(define-fun lo ((a (_ BitVec 64))) (_ BitVec 32)
((_ extract 31 0) (bvand a #x00000000FFFFFFFF)))

;; hi
(declare-fun hi ((_ BitVec 64)) (_ BitVec 32))

;; hi__def_axiom
(assert
(forall ((a (_ BitVec 64)))
(! (= (hi a) ((_ extract 31 0) (bvlshr a ((_ int2bv 64) 32)))) :pattern (
(hi
a)) )))

;; big
(declare-fun big1 ((_ BitVec 64)) Int)

(define-fun bv2nat64 ((a (_ BitVec 64))) Int
  (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
  (ite (= ((_ extract 0 0) a) (_ bv0 1)) 0 1)
  (ite (= ((_ extract 1 1) a) (_ bv0 1)) 0 2))
  (ite (= ((_ extract 2 2) a) (_ bv0 1)) 0 4))
  (ite (= ((_ extract 3 3) a) (_ bv0 1)) 0 8))
  (ite (= ((_ extract 4 4) a) (_ bv0 1)) 0 16))
  (ite (= ((_ extract 5 5) a) (_ bv0 1)) 0 32))
  (ite (= ((_ extract 6 6) a) (_ bv0 1)) 0 64))
  (ite (= ((_ extract 7 7) a) (_ bv0 1)) 0 128))
  (ite (= ((_ extract 8 8) a) (_ bv0 1)) 0 256))
  (ite (= ((_ extract 9 9) a) (_ bv0 1)) 0 512))
  (ite (= ((_ extract 10 10) a) (_ bv0 1)) 0 1024))
  (ite (= ((_ extract 11 11) a) (_ bv0 1)) 0 2048))
  (ite (= ((_ extract 12 12) a) (_ bv0 1)) 0 4096))
  (ite (= ((_ extract 13 13) a) (_ bv0 1)) 0 8192))
  (ite (= ((_ extract 14 14) a) (_ bv0 1)) 0 16384))
  (ite (= ((_ extract 15 15) a) (_ bv0 1)) 0 32768))
  (ite (= ((_ extract 16 16) a) (_ bv0 1)) 0 65536))
  (ite (= ((_ extract 17 17) a) (_ bv0 1)) 0 131072))
  (ite (= ((_ extract 18 18) a) (_ bv0 1)) 0 262144))
  (ite (= ((_ extract 19 19) a) (_ bv0 1)) 0 524288))
  (ite (= ((_ extract 20 20) a) (_ bv0 1)) 0 1048576))
  (ite (= ((_ extract 21 21) a) (_ bv0 1)) 0 2097152))
  (ite (= ((_ extract 22 22) a) (_ bv0 1)) 0 4194304))
  (ite (= ((_ extract 23 23) a) (_ bv0 1)) 0 8388608))
  (ite (= ((_ extract 24 24) a) (_ bv0 1)) 0 16777216))
  (ite (= ((_ extract 25 25) a) (_ bv0 1)) 0 33554432))
  (ite (= ((_ extract 26 26) a) (_ bv0 1)) 0 67108864))
  (ite (= ((_ extract 27 27) a) (_ bv0 1)) 0 134217728))
  (ite (= ((_ extract 28 28) a) (_ bv0 1)) 0 268435456))
  (ite (= ((_ extract 29 29) a) (_ bv0 1)) 0 536870912))
  (ite (= ((_ extract 30 30) a) (_ bv0 1)) 0 1073741824))
  (ite (= ((_ extract 31 31) a) (_ bv0 1)) 0 2147483648))
  (ite (= ((_ extract 32 32) a) (_ bv0 1)) 0 4294967296))
  (ite (= ((_ extract 33 33) a) (_ bv0 1)) 0 8589934592))
  (ite (= ((_ extract 34 34) a) (_ bv0 1)) 0 17179869184))
  (ite (= ((_ extract 35 35) a) (_ bv0 1)) 0 34359738368))
  (ite (= ((_ extract 36 36) a) (_ bv0 1)) 0 68719476736))
  (ite (= ((_ extract 37 37) a) (_ bv0 1)) 0 137438953472))
  (ite (= ((_ extract 38 38) a) (_ bv0 1)) 0 274877906944))
  (ite (= ((_ extract 39 39) a) (_ bv0 1)) 0 549755813888))
  (ite (= ((_ extract 40 40) a) (_ bv0 1)) 0 1099511627776))
  (ite (= ((_ extract 41 41) a) (_ bv0 1)) 0 2199023255552))
  (ite (= ((_ extract 42 42) a) (_ bv0 1)) 0 4398046511104))
  (ite (= ((_ extract 43 43) a) (_ bv0 1)) 0 8796093022208))
  (ite (= ((_ extract 44 44) a) (_ bv0 1)) 0 17592186044416))
  (ite (= ((_ extract 45 45) a) (_ bv0 1)) 0 35184372088832))
  (ite (= ((_ extract 46 46) a) (_ bv0 1)) 0 70368744177664))
  (ite (= ((_ extract 47 47) a) (_ bv0 1)) 0 140737488355328))
  (ite (= ((_ extract 48 48) a) (_ bv0 1)) 0 281474976710656))
  (ite (= ((_ extract 49 49) a) (_ bv0 1)) 0 562949953421312))
  (ite (= ((_ extract 50 50) a) (_ bv0 1)) 0 1125899906842624))
  (ite (= ((_ extract 51 51) a) (_ bv0 1)) 0 2251799813685248))
  (ite (= ((_ extract 52 52) a) (_ bv0 1)) 0 4503599627370496))
  (ite (= ((_ extract 53 53) a) (_ bv0 1)) 0 9007199254740992))
  (ite (= ((_ extract 54 54) a) (_ bv0 1)) 0 18014398509481984))
  (ite (= ((_ extract 55 55) a) (_ bv0 1)) 0 36028797018963968))
  (ite (= ((_ extract 56 56) a) (_ bv0 1)) 0 72057594037927936))
  (ite (= ((_ extract 57 57) a) (_ bv0 1)) 0 144115188075855872))
  (ite (= ((_ extract 58 58) a) (_ bv0 1)) 0 288230376151711744))
  (ite (= ((_ extract 59 59) a) (_ bv0 1)) 0 576460752303423488))
  (ite (= ((_ extract 60 60) a) (_ bv0 1)) 0 1152921504606846976))
  (ite (= ((_ extract 61 61) a) (_ bv0 1)) 0 2305843009213693952))
  (ite (= ((_ extract 62 62) a) (_ bv0 1)) 0 4611686018427387904))
  (ite (= ((_ extract 63 63) a) (_ bv0 1)) 0 9223372036854775808))
)

;; PROBLEMATIC DEFINITION
;; big__def_axiom
(assert
(forall ((arg (_ BitVec 64)))
(! (= (big1 arg) (bv2nat arg)) :pattern ((big1 arg)) )))

(declare-const mult Int)

(declare-const term_hi Int)

(declare-const term_mi1 Int)

(declare-const big_2xxsingle Int)

(declare-const dumdum Int)

(assert
(not
(forall ((t11 (_ BitVec 64)) (t2 (_ BitVec 64)))
(forall ((o61 uns32)) (=> (= (to_rep1 o61) (lo t2))

(= mult (+ (+ (+ (+ term_hi term_mi1) (+ (* (* big_2xxsingle big_2xxsingle)
(big1 ((_ zero_extend 32) (hi t11)))) (* (* big_2xxsingle big_2xxsingle) (big1
((_ zero_extend 32) (hi t2)))))) (* big_2xxsingle (big1 ((_ zero_extend 32)

(lo t2)

)))) dumdum))

(= mult (+ (+ (+ (+ term_hi term_mi1) (+ (* (* big_2xxsingle big_2xxsingle)
(big1 ((_ zero_extend 32) (hi t11)))) (* (* big_2xxsingle big_2xxsingle) (big1
((_ zero_extend 32) (hi t2)))))) (* big_2xxsingle (big1 ((_ zero_extend 32)

(to_rep1 o61)

)))) dumdum))

)))))

(check-sat)
