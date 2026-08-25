; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_FP)
(declare-const a Float64)
(declare-const b Float64)
(declare-const c Float64)
(assert
  (not
    (= (fp #b1
           #b11111111111
           #b1111111111111111111111111111111111111111111111111111)
       (fp.div RTP (fp.max a b) c))))
(check-sat)
