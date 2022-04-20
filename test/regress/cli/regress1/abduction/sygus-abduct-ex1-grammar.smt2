; COMMAND-LINE: --produce-abducts --sygus-stream --sygus-abort-size=3
; EXPECT: (error "Maximum term size (3) for enumerative SyGuS exceeded.")
; SCRUBBER: sed -e 's/.*(>= j (+ 1 1))/SPURIOUS/; s/(define-fun.*//; /^$/d'
; EXIT: 1

(set-logic QF_LIA)
(set-option :produce-abducts true)

(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= n 0) (>= m 0)))
(assert (< n i))
(assert (< (+ i j) m))

; This test ensures that (>= j (+ 1 1)) is not printed as a solution,
; since it is spurious: (>= j 0) is a stronger solution and will be enumerated
; first.
(get-abduct A 
  (<= n m)
  ((GA Bool) (GI Int))
  (
  (GA Bool ((>= GI GI)))
  (GI Int ((+ GI GI) (- GI) i j 0 1))
  )
)
