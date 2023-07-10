; COMMAND-LINE: --produce-interpolants --sygus-core-connective
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-logic ALL)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x 5))
(assert (> y 5))
(assert (> z 5))

(get-interpolant A (> (+ x y z) 0)
  ((GA Bool) (GB Int))
  (
  (GA Bool ((> GB GB) (= GB GB) (not GA) (and GA GA)))
  (GB Int ((+ GB GB)  x y z 0))
  )

)
