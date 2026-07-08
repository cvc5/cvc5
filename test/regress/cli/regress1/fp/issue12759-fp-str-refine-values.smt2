; EXPECT: sat
; Note: the strings-model-length warnings below are integral to this test:
; the oversized strings model is what corrupted the model values seen by the
; FP conversion-abstraction refinement (see cvc5/cvc5#12759). If the warning
; text (or the number of times it is emitted) changes, update these lines --
; but make sure the warning still triggers, otherwise this test no longer
; exercises the intended code path.
; EXPECT-ERROR: The model was computed to have strings of length 4294967295. Based on the current value of option --strings-model-max-len, we only allow strings up to length 65536
; EXPECT-ERROR: The model was computed to have strings of length 4294967295. Based on the current value of option --strings-model-max-len, we only allow strings up to length 65536
; DISABLE-TESTER: model
(set-logic QF_UFBVFPSLIRA)

(declare-fun c (String Int (_ FloatingPoint 8 24) (_ BitVec 32)) Int)
(declare-const s String)

(assert
  (str.is_digit
    (str.from_code
      (c s
         (to_int
           (fp.to_real
             ((_ to_fp 8 24) RTP ((_ int_to_bv 2) (str.to_code s)))
           )
         )
         (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
         ((_ int_to_bv 32) 0)
      )
    )
  )
)

(assert
  (= ""
    (str.at s
      (c s
         1
         (_ -zero 8 24)
         ((_ int_to_bv 32) (+ 1 (str.len s)))
      )
    )
  )
)

(check-sat)
