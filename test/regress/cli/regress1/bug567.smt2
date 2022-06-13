; COMMAND-LINE: --incremental --mbqi
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((OptInt0 0)) (((Some (value0 Int)) (None))))
(declare-datatypes ((List0 0)) (((Cons (head0 Int) (tail0 List0)) (Nil))))

(declare-fun errorValue2 () Bool)
(declare-fun errorValue1 () Bool)

(declare-fun size (List0) Int)
(declare-fun mergeInto (List0 List0) List0)
(declare-fun isSorted (List0) Bool)
(declare-fun buggySortedIns (Int List0) List0)
(declare-fun sortedIns (Int List0) List0)
(declare-fun sort (List0) List0)
(declare-fun contents (List0) (Set Int))

(assert (forall ((l List0)) (! (= (size l) (ite ((_ is Nil) l) 0 (+ 1 (size (tail0 l))))) :pattern ((size l)))))
(assert (forall ((l1 List0) (l2 List0)) (! (= (mergeInto l1 l2) (ite ((_ is Nil) l1) l2 (mergeInto (tail0 l1) (sortedIns (head0 l1) l2)))) :pattern ((mergeInto l1 l2)))))
(assert (forall ((l2 List0)) (! (= (isSorted l2) (ite ((_ is Nil) l2) true (ite (and ((_ is Cons) l2) ((_ is Nil) (tail0 l2))) true (ite (and ((_ is Cons) l2) ((_ is Cons) (tail0 l2))) (and (<= (head0 l2) (head0 (tail0 l2))) (isSorted (Cons (head0 (tail0 l2)) (tail0 (tail0 l2))))) errorValue1)))) :pattern ((isSorted l2)))))
(assert (forall ((l4 List0) (e1 Int)) (! (= (buggySortedIns e1 l4) (ite ((_ is Nil) l4) (Cons e1 Nil) (ite (<= (head0 l4) e1) (Cons (head0 l4) (buggySortedIns e1 (tail0 l4))) (Cons e1 l4)))) :pattern ((buggySortedIns e1 l4)))))
(assert (forall ((l3 List0) (e Int)) (! (= (sortedIns e l3) (ite ((_ is Nil) l3) (Cons e Nil) (ite (<= (head0 l3) e) (Cons (head0 l3) (sortedIns e (tail0 l3))) (Cons e l3)))) :pattern ((sortedIns e l3)))))
(assert (forall ((l5 List0)) (! (= (sort l5) (ite ((_ is Nil) l5) Nil (sortedIns (head0 l5) (sort (tail0 l5))))) :pattern ((sort l5)))))
(assert (forall ((l1 List0)) (! (= (contents l1) (ite ((_ is Nil) l1) (as set.empty (Set Int)) (set.union (contents (tail0 l1)) (set.singleton (head0 l1))))) :pattern ((contents l1)))))

(push)
(assert (forall ((l List0)) (not (let ((result (ite ((_ is Nil) l) 0 (+ 1 (size (tail0 l)))))) (>= result 0)))))
(check-sat)
(pop)

(push)
(assert (forall ((l2 List0)) (not (not (and (not ((_ is Nil) l2)) (not (and ((_ is Cons) l2) ((_ is Nil) (tail0 l2)))) (not (and ((_ is Cons) l2) ((_ is Cons) (tail0 l2)))))))))
(check-sat)
(pop)

(push)
(assert (forall ((l4 List0) (e1 Int)) (not (let ((result2 (ite ((_ is Nil) l4) (Cons e1 Nil) (ite (<= (head0 l4) e1) (Cons (head0 l4) (buggySortedIns e1 (tail0 l4))) (Cons e1 l4))))) (and (= (contents result2) (set.union (contents l4) (set.singleton e1))) (isSorted result2) (= (size result2) (+ (size l4) 1)))))))
(check-sat)
(pop)
