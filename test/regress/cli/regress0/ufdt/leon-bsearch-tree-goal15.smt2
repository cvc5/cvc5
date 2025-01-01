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

(declare-fun nmax (Nat Nat) Nat)
(assert (forall ((n Nat) (m Nat)) (= (nmax n m) (ite (less n m) m n))))

; lists      
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun len (Lst) Nat)
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))

(declare-fun mem (Nat Lst) Bool)
(assert (forall ((x Nat)) (not (mem x nil))))
(assert (forall ((x Nat) (y Nat) (z Lst)) (= (mem x (cons y z)) (or (= x y) (mem x z)))))

; (binary search) tree
(declare-datatype Tree ((node (data Nat) (left Tree) (right Tree)) (leaf)))

(declare-fun tinsert (Tree Nat) Tree)
(assert (forall ((i Nat)) (= (tinsert leaf i) (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Nat) (i Nat)) (= (tinsert (node d l r) i) (ite (less d i) (node d l (tinsert r i)) (node d (tinsert l i) r)))))

(declare-fun height (Tree) Nat)
(assert (= (height leaf) zero))
(assert (forall ((x Nat) (y Tree) (z Tree)) (= (height (node x y z)) (succ (nmax (height y) (height z))))))

(declare-fun tinsert-all (Tree Lst) Tree)
(assert (forall ((x Tree)) (= (tinsert-all x nil) x)))
(assert (forall ((x Tree) (n Nat) (l Lst)) (= (tinsert-all x (cons n l)) (tinsert (tinsert-all x l) n))))

(declare-fun tsize (Tree) Nat)
(assert (= (tsize leaf) zero))
(assert (forall ((x Nat) (l Tree) (r Tree)) (= (tsize (node x l r)) (succ (plus (tsize l) (tsize r))))))

(declare-fun tremove (Tree Nat) Tree)
(assert (forall ((i Nat)) (= (tremove leaf i) leaf)))
(assert (forall ((i Nat) (d Nat) (l Tree) (r Tree)) (=> (less i d) (= (tremove (node d l r) i) (node d (tremove l i) r)))))
(assert (forall ((i Nat) (d Nat) (l Tree) (r Tree)) (=> (less d i) (= (tremove (node d l r) i) (node d l (tremove r i))))))
(assert (forall ((d Nat) (r Tree)) (= (tremove (node d leaf r) d) r)))
(assert (forall ((d Nat) (ld Nat) (ll Tree) (lr Tree) (r Tree)) (= (tremove (node d (node ld ll lr) r) d) (node ld (tremove (node ld ll lr) ld) r))))

(declare-fun tremove-all (Tree Lst) Tree)
(assert (forall ((x Tree)) (= (tremove-all x nil) x)))
(assert (forall ((x Tree) (n Nat) (l Lst)) (= (tremove-all x (cons n l)) (tremove-all (tremove x n) l))))

(declare-fun tcontains (Tree Nat) Bool)
(assert (forall ((i Nat)) (not (tcontains leaf i))))
(assert (forall ((d Nat) (l Tree) (r Tree) (i Nat)) (= (tcontains (node d l r) i) (or (= d i) (tcontains l i) (tcontains r i)))))

(declare-fun tsorted (Tree) Bool)
(assert (tsorted leaf))
(assert (forall ((d Nat) (l Tree) (r Tree)) (= (tsorted (node d l r)) (and (tsorted l) (tsorted r)
                                                                           (forall ((x Nat)) (=> (tcontains l x) (leq x d)))
                                                                           (forall ((x Nat)) (=> (tcontains r x) (less d x)))))))
                                                                           
(declare-fun tmember (Tree Nat) Bool)
(assert (forall ((x Nat)) (not (tmember leaf x))))
(assert (forall ((d Nat) (l Tree) (r Tree) (i Nat)) (= (tmember (node d l r) i) (ite (= i d) true (tmember (ite (less d i) r l) i)))))
                              
(declare-fun content (Tree) Lst)
(assert (= (content leaf) nil))
(assert (forall ((d Nat) (l Tree) (r Tree)) (= (content (node d l r)) (append (content l) (cons d (content r))))))

; proven
(assert 
(forall ((t Tree) (n Nat)) (= (tsize (tinsert t n)) (succ (tsize t)))) ; G-bsearch-tree-1 
)
(assert 
(forall ((l Lst) (t Tree)) (leq (tsize t) (tsize (tinsert-all t l)))) ; G-bsearch-tree-2 
)
(assert 
(forall ((l Lst) (t Tree)) (= (tsize (tinsert-all t l)) (plus (tsize t) (len l)))) ; G-bsearch-tree-3 
)
(assert 
(forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t))) ; G-bsearch-tree-4 
)
(assert 
(forall ((l Lst) (t Tree)) (leq (tsize (tremove-all t l)) (tsize t))) ; G-bsearch-tree-5 
)
(assert 
(forall ((x Tree) (i Nat)) (tcontains (tinsert x i) i)) ; G-bsearch-tree-6 
)
(assert 
(forall ((i Nat) (x Tree) (j Nat)) (= (or (= i j) (tcontains x j)) (tcontains (tinsert x i) j))) ; G-bsearch-tree-7 
)
(assert 
(forall ((x Tree) (i Nat)) (=> (tsorted x) (tsorted (tinsert x i)))) ; G-bsearch-tree-8 
)
(assert 
(forall ((x Tree) (i Nat)) (tmember (tinsert x i) i)) ; G-bsearch-tree-9 
)
(assert 
(forall ((i Nat) (x Tree) (j Nat)) (= (or (= i j) (tmember x j)) (tmember (tinsert x i) j))) ; G-bsearch-tree-10 
)
(assert 
(forall ((i Nat) (x Tree)) (=> (tsorted x) (= (tcontains x i) (tmember x i)))) ; G-bsearch-tree-11 
)
(assert 
(forall ((i Nat) (x Tree)) (=> (tmember x i) (tcontains x i))) ; G-bsearch-tree-12 
)
(assert 
(forall ((l Lst) (x Tree) (n Nat)) (= (tinsert-all (tinsert x n) l) (tinsert-all x (append l (cons n nil))))) ; G-bsearch-tree-13 
)
(assert 
(forall ((x Lst)) (tsorted (tinsert-all leaf x))) ; G-bsearch-tree-14 
)

; conjecture
(assert (not 
(forall ((x Lst) (i Nat)) (= (mem i x) (tcontains (tinsert-all leaf x) i))) ; G-bsearch-tree-15 
))
(check-sat)
