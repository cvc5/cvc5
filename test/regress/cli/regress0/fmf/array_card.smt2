; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic AUFLIA)
(set-option :produce-models true)
(declare-sort U 0)
(declare-fun f () (Array U U))
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)

(assert (distinct a b c))

(assert (distinct (select f a) (select f b)))

(assert (forall ((x U)) (or (= (select f x) c) (= (select f x) b))))

(check-sat)
