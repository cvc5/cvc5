; COMMAND-LINE:
; COMMAND-LINE: --check-proofs
; EXPECT: sat
(set-logic QF_FPNRA)

(declare-fun t () Real)

(assert (> t (/ 31415926 10000000)))
(assert (< t (/ 31415927 10000000)))

(assert
  (or
    (> t 0)
    (= 0.0
       (fp.to_real
         ((_ to_fp 8 24) RNE t)))))

(check-sat)
