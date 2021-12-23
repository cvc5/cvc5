; EXPECT: sat

; Observed behavior:
;   --check-model failed for set-term (bag.union_disjoint (z3f69 z3v151) (bag z3v143 1))
; with different set of elements in the model for representative and the node
; itself.
;
; Issue:
;   The trouble with data structure being mainted to ensure that things
; for which lemmas have been generated are not generated again. This
; data structure (d_pendingEverInserted) needs to be user context
; dependent. The bug was in the sequence of steps from requesting that
; a lemma be generated to when it actually was. Sequence was:
; addToPending (and also adds to pending ever inserted) ->
; isComplete (might remove things from pending if requirment met in other ways) ->
; getLemma (actually generated the lemma, if requirement not already met)
;
; Resolution:
;   adding terms to d_pendingEverInserted was moved from addToPending()
; to getLemma().

(set-logic QF_ALL)

(set-info :status sat)

(define-sort Elt () Int)
(define-sort mySet () (Bag Elt))

(define-fun smt_set_emp () mySet (as bag.empty mySet))
(define-fun smt_set_mem ((x Elt) (s mySet)) Bool (>= (bag.count x s) 1))
(define-fun smt_set_add ((s mySet) (x Elt)) mySet (bag.union_disjoint s (bag x 1)))
(define-fun smt_set_cup ((s1 mySet) (s2 mySet)) mySet (bag.union_disjoint s1 s2))
(define-fun smt_set_cap ((s1 mySet) (s2 mySet)) mySet (bag.inter_min s1 s2))

;(define-fun smt_set_com ((s mySet)) mySet ((_ map not) s))
(define-fun smt_set_dif ((s1 mySet) (s2 mySet)) mySet (bag.difference_remove s1 s2))

;(define-fun smt_set_sub ((s1 mySet) (s2 mySet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-fun smt_set_sub ((s1 mySet) (s2 mySet)) Bool (bag.subbag s1 s2))

(declare-fun z3v58 () Int)
(declare-fun z3v59 () Int)

(assert (distinct z3v58 z3v59))

(declare-fun z3f60 (Int) Bool)
(declare-fun z3v61 () Int)
(declare-fun z3f62 (Int) Int)
(declare-fun z3v63 () Int)
(declare-fun z3v64 () Int)
(declare-fun z3v67 () Int)
(declare-fun z3f68 (Int) Int)
(declare-fun z3f69 (Int) mySet)
(declare-fun z3f70 (Int) mySet)
(declare-fun z3f71 (Int) Bool)
(declare-fun z3v90 () Int)
(declare-fun z3v91 () Int)
(declare-fun z3f92 (Int Int) Int)
(declare-fun z3v140 () Int)
(declare-fun z3v141 () Int)
(declare-fun z3v142 () Int)
(declare-fun z3v143 () Int)
(declare-fun z3v144 () Int)
(declare-fun z3v145 () Int)
(declare-fun z3v147 () Int)
(declare-fun z3v150 () Int)
(declare-fun z3v151 () Int)
(declare-fun z3v152 () Int)

(assert
  (not
    (= (z3f69 z3v152)
       (z3f69 z3v140))))

(assert
  (= (z3f69 z3v151)
     (smt_set_cup (z3f69 z3v141)
                  (z3f69 z3v140))))

(assert
  (= (z3f69 z3v152)
     (smt_set_cup (bag z3v143 1) (z3f69 z3v151))))

(assert
  (= (z3f70 z3v152)
     (smt_set_cup (bag z3v143 1) (z3f70 z3v151))))

(assert
  (and
   (= (z3f69 z3v142)
      (smt_set_cup (bag z3v143 1) (z3f69 z3v141)))
   (= (z3f70 z3v142)
      (smt_set_cup (bag z3v143 1) (z3f70 z3v141)))
   (= z3v142 (z3f92 z3v143 z3v141))
   (= z3v142 z3v144)
   (= (z3f62 z3v61) z3v61)
   (= (z3f62 z3v63) z3v63)))

(check-sat)
