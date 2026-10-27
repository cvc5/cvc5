; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: (error "Error in option parsing: replay-early-close-depth = 0 is not a legal setting, value should be at least 1.")
; EXPECT: unsat
;; An out-of-range replay-early-close-depth must be rejected at option-parse
;; time. Without the bound, a value < 1 reaches "depth % replayEarlyCloseDepths"
;; in TheoryArithPrivate::replayLogRec: Assert(... >= 1) in assertions builds,
;; and a real integer division-by-zero (SIGFPE) in production builds. The body
;; recurses into replayLogRec, which is where the crash lives.
(set-logic QF_LIA)
(set-option :replay-early-close-depth 0)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(assert (<= -5 x0))
(assert (<= x0 5))
(assert (<= -5 x1))
(assert (<= x1 5))
(assert (<= -5 x2))
(assert (<= x2 5))
(assert (<= -5 x3))
(assert (<= x3 5))
(assert (<= -5 x4))
(assert (<= x4 5))
(assert (= (+ (* 70241 x0) (* 76389 x1) (* 66512 x2) (* 11267 x3) (* 9158 x4)) 82))
(assert (= (+ (* 55644 x0) (* 74117 x1) (* (- 29262) x2) (* (- 76416) x3) (* (- 75644) x4)) -175))
(check-sat)
