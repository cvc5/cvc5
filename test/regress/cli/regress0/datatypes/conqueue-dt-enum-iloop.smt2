; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun start!13 () Bool)

(assert start!13)

(declare-fun b!39 () Bool)

(declare-sort T!14 0)

(declare-datatypes ((LazyConQ!5 0) (Conc!6 0) (ConQ!6 0)) (
(
  (Lazyarg1!5 (carry!37 Conc!6) (srear!9 LazyConQ!5))
  (Lazyarg2!5 (t!270 ConQ!6))
  (Lazyarg3!5 (carry!38 Conc!6) (t!271 ConQ!6))
  (Lazyarg4!5 (tree!19 Conc!6) (carry!39 Conc!6))
  (Lazyarg5!5 (tree!20 Conc!6) (carry!40 Conc!6))
  (PushLeft!5 (ys!22 Conc!6) (xs!60 LazyConQ!5))
  (PushLeftLazy!5 (ys!23 Conc!6) (xs!61 LazyConQ!5)))
(
  (CC!5 (left!9 Conc!6) (right!9 Conc!6))
  (Empty!5)
  (Single!5 (x!106 T!14)))
(
  (Spine!5 (head!10 Conc!6) (rear!5 LazyConQ!5))
  (Tip!5 (t!272 Conc!6)))
))

(declare-fun e!41 () LazyConQ!5)

(declare-fun l!2 () LazyConQ!5)

(declare-fun st!3 () (Set LazyConQ!5))

(declare-fun firstUnevaluated!3 (LazyConQ!5 (Set LazyConQ!5)) LazyConQ!5)

(declare-fun evalLazyConQ2!7 (LazyConQ!5) ConQ!6)

(assert (=> b!39 (= e!41 (firstUnevaluated!3 (rear!5 (evalLazyConQ2!7 l!2)) st!3))))

(declare-fun b!40 () Bool)

(declare-fun e!42 () LazyConQ!5)

(assert (=> b!40 (= e!42 e!41)))

(assert (=> b!40 (= b!39 ((_ is Spine!5) (evalLazyConQ2!7 l!2)))))

(declare-fun b!41 () Bool)

(assert (=> b!40 (or (not b!39) (not b!41))))

(assert (=> b!40 (or b!39 b!41)))

(assert (=> b!41 (= e!41 l!2)))

(declare-fun b!42 () Bool)

(assert (=> b!42 (= e!42 l!2)))

(declare-fun lt!14 () LazyConQ!5)

(declare-fun isTip!5 (ConQ!6) Bool)

(assert (=> start!13 (and (not (isTip!5 (evalLazyConQ2!7 lt!14))) (set.member lt!14 st!3))))

(assert (=> start!13 (= lt!14 e!42)))

(assert (=> start!13 (= b!40 (set.member l!2 st!3))))

(assert (=> start!13 (or (not b!40) (not b!42))))

(assert (=> start!13 (or b!40 b!42)))

(check-sat)
