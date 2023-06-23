; COMMAND-LINE: -o timeout-core-benchmark --timeout-core-timeout=500
; REQUIRES: no-competition
; EXPECT: ;; timeout core
; EXPECT: (set-logic ALL)
; EXPECT: (declare-fun x () Int)
; EXPECT: (assert (= (* x x x) 564838384999))
; EXPECT: (check-sat)
; EXPECT: ;; end timeout core
; EXPECT: unknown
; EXPECT: (
; EXPECT: hard
; EXPECT: )
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(assert (! (> u 0) :named u0))
(assert (! (< w 0) :named w0))
(assert (! (= (* x x x) 564838384999) :named hard))
(get-timeout-core)
