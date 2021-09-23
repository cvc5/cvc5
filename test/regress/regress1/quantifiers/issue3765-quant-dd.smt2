; COMMAND-LINE: --finite-model-find
; EXPECT: sat

(set-logic ALL)

(declare-sort U 0)
(declare-fun g (U) Int)
(declare-sort V 0)
(declare-fun f (V) Int)
(assert (and 
(forall ((?i U)) (not (forall ((?z V)) (not (= (f ?z) (div (- 1) (g ?i))))) ))
))

(declare-fun k () U)
(assert (= (g k) 22))


(check-sat)
