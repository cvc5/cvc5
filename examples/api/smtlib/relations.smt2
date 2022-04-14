(set-logic ALL)

(set-option :produce-models true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; we need sets extension to support set.universe operator
(set-option :sets-ext true)

(declare-sort Person 0)

(declare-fun people () (Relation Person))
(declare-fun males () (Relation Person))
(declare-fun females () (Relation Person))
(declare-fun father () (Relation Person Person))
(declare-fun mother () (Relation Person Person))
(declare-fun parent () (Relation Person Person))
(declare-fun ancestor () (Relation Person Person))
(declare-fun descendant () (Relation Person Person))

(assert (= people (as set.universe (Relation Person))))
(assert (not (= males (as set.empty (Relation Person)))))
(assert (not (= females (as set.empty (Relation Person)))))
(assert (= (set.inter males females) (as set.empty (Relation Person))))

; father relation is not empty
(assert (not (= father (as set.empty (Relation Person Person)))))
; mother relation is not empty
(assert (not (= mother (as set.empty (Relation Person Person)))))
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
