; COMMAND-LINE: --finite-model-find
; EXPECT: sat
; this problem produced a model where incorrectly card(a)=1 due to --mbqi=fmc
(set-logic ALL)

(declare-sort a 0)
(declare-datatypes ((tree 0)) (((Leaf (lab a)))))

(declare-sort alpha 0)
(declare-fun alphabet (tree a) Bool)
(declare-fun g1 (alpha) tree)
(declare-fun g2 (alpha) a)

(assert
 (forall ((x alpha))
    (=>
     (= (lab (g1 x)) (g2 x))
     (alphabet (g1 x) (g2 x)))))

(declare-fun x () a)
(declare-fun y () a)
; (assert (= x y))
(assert
  (and
   (exists ((b alpha)) (and (= (Leaf y) (g1 b)) (= x (g2 b))))
   (not (alphabet (Leaf y) x))))
(check-sat)
