; COMMAND-LINE:
; COMMAND-LINE: --check-proofs
; EXPECT: sat
(set-logic ALL)
(define-fun t () (_ BitVec 32)
  ((_ fp.to_ubv 32) RNE (fp (_ bv0 1) (_ bv255 8) (_ bv1 23))))

(assert (=
  (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) ; LHS: +0.0
  ((_ to_fp 8 24)
    (bvand (_ bv1 32)
      ((_ fp.to_ubv 32) RNE
        (fp.mul RTZ (_ +zero 8 24)
          ((_ to_fp 8 24) RTZ
            (+ 1.0
              (fp.to_real
                ((_ to_fp 8 24)
                  (bvand #x007FFFFF t)
                )
              )
            )
          )
        )
      )
    )
  )
))

(check-sat)
