; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
; natural numbers
(declare-datatype Nat ((succ (pred Nat)) (zero)))

(declare-fun less (Nat Nat) Bool)
(assert (not (less zero zero)))
(assert (forall ((x Nat)) (less zero (succ x))))
(assert (forall ((x Nat) (y Nat)) (= (less (succ x) (succ y)) (less x y))))

(define-fun leq ((x Nat) (y Nat)) Bool (or (= x y) (less x y)))

(declare-fun plus (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (plus zero n) n)))
(assert (forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m)))))

; lists      
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))

(declare-fun len (Lst) Nat)
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))

(declare-fun rsorted (Lst) Bool)
(assert (rsorted nil))
(assert (forall ((x Nat)) (rsorted (cons x nil))))
(assert (forall ((x Nat) (z Nat) (y Lst)) (= (rsorted (cons x (cons z y))) (and (rsorted (cons z y)) (leq z x)))))

(declare-fun sorted (Lst) Bool)
(assert (sorted nil))
(assert (forall ((x Nat)) (sorted (cons x nil))))
(assert (forall ((x Nat) (z Nat) (y Lst)) (= (sorted (cons x (cons z y))) (and (rsorted (cons z y)) (leq x z)))))

; heaps
(declare-datatype Heap ((hleaf) (heap (rk Nat) (value Nat) (hleft Heap) (hright Heap))))

(declare-fun rightHeight (Heap) Nat)
(assert (= (rightHeight hleaf) zero))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (rightHeight (heap k v l r)) (succ (rightHeight r)))))

(declare-fun rank (Heap) Nat)
(assert (= (rank hleaf) zero))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (rank (heap k v l r)) k)))

(declare-fun hasLeftistProperty (Heap) Bool)
(assert (hasLeftistProperty hleaf))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (hasLeftistProperty (heap k v l r)) (and (hasLeftistProperty l) (hasLeftistProperty r) 
                                                                                                (leq (rightHeight r) (rightHeight l)) 
                                                                                                (= k (succ (rightHeight r)))))))
                                                                                                
(declare-fun hsize (Heap) Nat)
(assert (= (hsize hleaf) zero))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (hsize (heap k v l r)) (succ (plus (hsize l) (hsize r))))))

(declare-fun mergea (Nat Heap Heap) Heap)
(assert (forall ((v Nat) (l Heap) (r Heap)) (= (mergea v l r) (ite (leq (rank r) (rank l)) (heap (succ (rank r)) v l r) (heap (succ (rank l)) v r l)))))

(declare-fun merge (Heap Heap) Heap)
(assert (forall ((h Heap)) (= (merge h hleaf) h)))
(assert (forall ((h Heap)) (= (merge hleaf h) h)))
(assert (forall ((k1 Nat) (v1 Nat) (l1 Heap) (r1 Heap) (k2 Nat) (v2 Nat) (l2 Heap) (r2 Heap)) (= (merge (heap k1 v1 l1 r1) (heap k2 v2 l2 r2)) 
                                                                                                 (ite (less v2 v1) 
                                                                                                      (mergea v1 l1 (merge r1 (heap k2 v2 l2 r2)))
                                                                                                      (mergea v2 l2 (merge (heap k1 v1 l1 r1) r2))))))
                                                                                                      
(declare-fun hinsert (Heap Nat) Heap)                                                                                                      
(assert (forall ((h Heap) (n Nat)) (= (hinsert h n) (merge (heap (succ zero) n hleaf hleaf) h))))

(declare-fun hinsert-all (Lst Heap) Heap)
(assert (forall ((h Heap)) (= (hinsert-all nil h) h)))
(assert (forall ((h Heap) (n Nat) (l Lst)) (= (hinsert-all (cons n l) h) (hinsert (hinsert-all l h) n))))

(declare-fun qheapsorta (Heap Lst) Lst)
(assert (forall ((l Lst)) (= (qheapsorta hleaf l) l)))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap) (x Lst)) (= (qheapsorta (heap k v l r) x) (qheapsorta (merge l r) (cons v x)))))

(declare-fun qheapsort (Lst) Lst)
(assert (forall ((l Lst)) (= (qheapsort l) (qheapsorta (hinsert-all l hleaf) nil))))

(declare-fun heapsorta (Heap) Lst)
(assert (= (heapsorta hleaf) nil))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (heapsorta (heap k v l r)) (cons v (heapsorta (merge l r))))))

(declare-fun heapsort (Lst) Lst)
(assert (forall ((l Lst)) (= (heapsort l) (heapsorta (hinsert-all l hleaf)))))

; proven
(assert 
(forall ((x Heap) (n Nat)) (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert x n)))) ; G-heap-1 
)

; conjecture
(assert (not 
(forall ((n Lst) (x Heap)) (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert-all n x)))) ; G-heap-2 
))
(check-sat)
