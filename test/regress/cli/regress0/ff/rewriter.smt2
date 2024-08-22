; REQUIRES: cocoa
; EXPECT: unsat
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(declare-fun x () (_ FiniteField 5))
(assert (or
  ; direct !=
  (= #f2m5 #f1m5 )
  ; direct ==
  (not (= #f1m5 #f1m5 ))
  ; neg: all constants
  (not (= (ff.neg #f1m5) #f4m5 ))
  ; add: all constants
  (not (= (ff.add #f0m5 #f1m5 #f2m5 #f3m5) #f1m5 ))
  ; add: vars cancel (w/ neg)
  (not (= (ff.add #f0m5 (ff.neg x) x) #f0m5 ))
  ; add: vars cancel
  (not (= (ff.add #f0m5 (ff.mul #f4m5 x) x) #f0m5 ))
  ; mul: a direct zero
  (= (ff.mul #f0m5 #f1m5 #f2m5 #f3m5) #f1m5 )
  ; mul: a direct zero w/ var
  (= (ff.mul #f0m5 #f1m5 x #f3m5) #f1m5 )
  ; mul: all constants
  (not (= (ff.mul #f1m5 #f2m5 #f3m5) #f1m5 ))
  ; mul: a direct zero w/ var
  (not (= (ff.mul x #f3m5) (ff.add x x x)))
  ; mul: a direct zero w/ monomials
  (not (= (ff.mul x x #f3m5) (ff.add (ff.mul x x) (ff.mul #f2m5 x x))))
))
(check-sat)
