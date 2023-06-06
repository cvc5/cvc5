; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(declare-const x Float64)
(define-fun f ((_f4_0 Bool)) Bool (fp.isSubnormal (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))
(assert (fp.isSubnormal (fp.div RTZ x (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(find-synth :rewrite_input)
