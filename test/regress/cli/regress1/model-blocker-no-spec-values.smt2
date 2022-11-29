; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(set-option :finite-model-find true)
(set-option :produce-models true)
(set-option :incremental true)
(declare-sort UInt 0)
(declare-fun intValue (UInt) Int)
(declare-fun idenInt () (Set (Tuple UInt UInt)))

; Identity relation definition for idenInt
(assert
 (forall ((x UInt)(y UInt))
         (=
          (set.member
           (tuple x y) idenInt;
           )
          (= x y))))

; intValue is injective
(assert
 (forall ((x UInt)(y UInt))
         (=>
          (not
           (= x y))
          (not
           (= (intValue x) (intValue y))))))

(check-sat)
(block-model :values)
(check-sat)
