(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-info :status sat)

(define-fun byte_2_int ((s String)) Int (ite (= (str.len s) 1) (str.code s) 256))

(define-fun read_buffer16 ((s1 String) (s2 String)) Int
  (+ (* 256 (byte_2_int s1)) 
     (byte_2_int s2))
)


(define-fun read_buffer32 ((s1 String) (s2 String) (s3 String) (s4 String)) Int
  (+ (+ (+ (* 16777216 (byte_2_int s1) )
           (*    65536 (byte_2_int s2) ) )
           (*      256 (byte_2_int s3) ) )
           (byte_2_int s4) )
)


(declare-const magic String)
(declare-const p1 String)
(declare-const p2 String)
(declare-const p3 String)
(declare-const size1 String)
(declare-const size2 String)
(declare-const size3 String)
(declare-const size4 String)
(declare-const off1 String)
(declare-const off2 String)
(declare-const off3 String)
(declare-const off4 String)
(assert (= magic "ABCD"))
(assert (= 1 (str.len size1)))
(assert (= 1 (str.len size2)))
(assert (= 1 (str.len size3)))
(assert (= 1 (str.len size4)))
(assert (= 1 (str.len off1)))
(assert (= 1 (str.len off2)))
(assert (= 1 (str.len off3)))
(assert (= 1 (str.len off4)))


(declare-const p3_off Int)
(declare-const before_p3 String)
(assert (= before_p3 (str.++ p1 p2)))
(assert (not (str.contains before_p3 magic)))
(assert (= p3_off (str.len before_p3)))


(declare-const p2_size   Int)
(declare-const p2_off    Int)
(declare-const p2_min_size  Int)
(assert (= p2_size  (read_buffer32  size1  size2  size3  size4)))
(assert (= p2_off   (read_buffer32  off1   off2   off3   off4)))
(assert (<= (+ p2_size p2_off) p3_off))
(assert (>= p2_size p2_min_size))
(assert (= p2_min_size 10))

(check-sat)
