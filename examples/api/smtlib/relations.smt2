(set-logic ALL)

(set-option :produce-models true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; we need sets extension to support set.universe operator
(set-option :sets-ext true)

(declare-sort Person 0)

(declare-fun people () (Set (Tuple Person)))
(declare-fun males () (Set (Tuple Person)))
(declare-fun females () (Set (Tuple Person)))
(declare-fun father () (Set (Tuple Person Person)))
(declare-fun mother () (Set (Tuple Person Person)))
(declare-fun parent () (Set (Tuple Person Person)))
(declare-fun ancestor () (Set (Tuple Person Person)))
(declare-fun descendant () (Set (Tuple Person Person)))

(assert (= people (as set.universe (Set (Tuple Person)))))
(assert (not (= males (as set.empty (Set (Tuple Person))))))
(assert (not (= females (as set.empty (Set (Tuple Person))))))
(assert (= (set.inter males females) (as set.empty (Set (Tuple Person)))))

; father relation is not empty
(assert (not (= father (as set.empty (Set (Tuple Person Person))))))
; mother relation is not empty
(assert (not (= mother (as set.empty (Set (Tuple Person Person))))))
; fathers are males
(assert (set.subset (rel.join father people) males))
; mothers are females
(assert (set.subset (rel.join mother people) females))
; parent
(assert (= parent (set.union father mother)))
; no self ancestor
(assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
; ancestor
(assert (= ancestor (rel.tclosure parent)))
; ancestor
(assert (= descendant (rel.transpose ancestor)))

(check-sat)
(get-model)
