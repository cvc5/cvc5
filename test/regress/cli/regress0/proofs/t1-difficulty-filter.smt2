; COMMAND-LINE: --dump-difficulty --produce-proofs
; SCRUBBER: sed 's/(.*//g;s/).*//g'
; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-logic UFLIA)
(declare-fun f (Int) Int) 
(declare-fun g (Int) Int) 
(declare-fun h (Int) Int)
(declare-fun a () Int) 
(declare-fun b () Int) 
(declare-fun c () Int)
(assert (forall ((x Int)) (> (f x) 5)))
(assert (forall ((x Int)) (> (h x) 0)))
(assert (forall ((x Int)) (> (g x) 0)))
(assert (or (< (f a) 0) (> (h a) 0) (< (h b) 0) (< (g a) 0)))
(assert (or (< (f c) 0) (< (h c) 0) (< (g b) 0)))
(assert (or (< (f b) 0) (< (h c) 0) (< (g c) 0)))
(check-sat)
