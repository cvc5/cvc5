; COMMAND-LINE: --model-u-print=decl-fun
; EXPECT: (declare-fun @a0 () us_image)
; EXPECT: (declare-fun @a0 () ||)
; SCRUBBER: sed -e '/declare-fun/!d; s/declare-fun [^[:space:]]*/declare-fun gt/g'
(set-option :produce-models true)
(set-logic QF_UF)
(declare-sort us_image 0)
(declare-sort || 0)
(check-sat)
(get-model)
