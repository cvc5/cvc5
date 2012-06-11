(set-logic LRA)

;; DATATYPE
;;   nat = succ(pred : nat) | zero,
;;   list = cons(car : tree, cdr : list) | null,
;;   tree = node(children : list) | leaf(data : nat)
;; END;

;;;;;;;;;;;
;; nat   ;;
;;;;;;;;;;;
(declare-sort nat 0)
(declare-fun zero () nat)
(declare-fun succ (nat) nat)

;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj1 (nat) nat)
(assert (forall ((?x1 nat))
                (! (! (=> true (=> true (= (inj1 (succ ?x1)) ?x1))) :pattern ((succ ?x1)) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun pred (nat) nat)
(assert (forall ((?x1 nat))
                (! (= (pred (succ ?x1)) ?x1) :rewrite-rule) ))

(assert (= (pred zero) zero))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_succ (nat) Bool)
(assert (= (is_succ zero) false))
(assert (forall ((?x1 nat))
                (! (! (=> true (=> true (= (is_succ (succ ?x1)) true))) :pattern ((succ ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 nat))
                (! (! (=> true (=> (is_succ ?x1) (= ?x1 (succ (pred ?x1))))) :pattern ((pred ?x1)) ) :rewrite-rule) ))

(declare-fun is_zero (nat) Bool)
(assert (= (is_zero zero) true))
(assert (forall ((?x1 nat))
                (! (=> true (=> (is_zero ?x1) (= ?x1 zero))) :rewrite-rule) ))

;;; directrr
(assert (forall ((?x1 nat))
                (! (= (is_succ (succ ?x1)) true) :rewrite-rule)))
(assert (forall ((?x1 nat))
                (! (= (is_zero (succ ?x1)) false) :rewrite-rule)))


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 nat))
                (! (=> (is_zero ?x1) (not (is_succ ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (=> (is_succ ?x1) (not (is_zero ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (=> (not (is_zero ?x1)) (is_succ ?x1) ) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (=> (not (is_succ ?x1)) (is_zero ?x1) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 nat))
                (! (! (=> true (or (is_zero ?x1) (is_succ ?x1))) :pattern ((pred ?x1)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_nat (nat) Real)
(assert (forall ((?x1 nat))
                (! (! (=> true (> (size_nat (succ ?x1)) (size_nat ?x1))) :pattern ((succ ?x1)) ) :rewrite-rule) ))



;;;;;;;;;;;;;;;;;;;;;
;; list and tree

(declare-sort list 0)
(declare-sort tree 0)

;;;;;;;;;;;
;; list  ;;
;;;;;;;;;;;

(declare-fun null () list)
(declare-fun cons (tree list) list)

(declare-fun node (list) tree)
(declare-fun leaf (nat) tree)

;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj2 (list) tree)
(assert (forall ((?x1 tree) (?x2 list))
                (! (! (=> true (=> true (= (inj2 (cons ?x1 ?x2)) ?x1))) :pattern ((cons ?x1 ?x2)) ) :rewrite-rule) ))

(declare-fun inj3 (list) list)
(assert (forall ((?x1 tree) (?x2 list))
                (! (! (=> true (=> true (= (inj3 (cons ?x1 ?x2)) ?x2))) :pattern ((cons ?x1 ?x2)) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun car (list) tree)
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (car (cons ?x1 ?x2)) ?x1) :rewrite-rule) ))

(assert (= (car null) (node null)))

(declare-fun cdr (list) list)
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (cdr (cons ?x1 ?x2)) ?x2) :rewrite-rule) ))

(assert (= (cdr null) null))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_cons (list) Bool)
(assert (= (is_cons null) false))
(assert (forall ((?x1 tree) (?x2 list))
                (! (! (=> true (=> true (= (is_cons (cons ?x1 ?x2)) true))) :pattern ((cons ?x1 ?x2)) ) :rewrite-rule) ))

(assert (forall ((?x1 list))
                (! (! (=> true (=> (is_cons ?x1) (= ?x1 (cons (car ?x1) (cdr ?x1))))) :pattern ((car ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (! (=> true (=> (is_cons ?x1) (= ?x1 (cons (car ?x1) (cdr ?x1))))) :pattern ((cdr ?x1)) ) :rewrite-rule) ))

(declare-fun is_null (list) Bool)
(assert (= (is_null null) true))

(assert (forall ((?x1 list))
                (! (! (=> true (=> (is_null ?x1) (= (car ?x1) (node null)))) :pattern ((car ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (! (=> true (=> (is_null ?x1) (= (cdr ?x1) null))) :pattern ((cdr ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 list))
                (! (=> true (=> (is_null ?x1) (= ?x1 null))) :rewrite-rule) ))

;;; directrr
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (is_cons (cons ?x1 ?x2)) true) :rewrite-rule) ))
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (is_null (cons ?x1 ?x2)) false) :rewrite-rule) ))



;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 list))
                (! (=> (is_null ?x1) (not (is_cons ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (=> (is_cons ?x1) (not (is_null ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (=> (not (is_null ?x1)) (is_cons ?x1) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (=> (not (is_cons ?x1)) (is_null ?x1) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 list))
            (! (! (=> true (or (is_null ?x1) (is_cons ?x1))) :pattern ((car ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
            (! (! (=> true (or (is_null ?x1) (is_cons ?x1))) :pattern ((cdr ?x1)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;
;; tree

;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj4 (tree) list)
(assert (forall ((?x1 list))
                (! (! (=> true (=> true (= (inj4 (node ?x1)) ?x1))) :pattern ((node ?x1)) ) :rewrite-rule) ))

(declare-fun inj5 (tree) nat)
(assert (forall ((?x1 nat))
                (! (! (=> true (=> true (= (inj5 (leaf ?x1)) ?x1))) :pattern ((leaf ?x1)) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun children (tree) list)
(assert (forall ((?x1 list))
                (! (= (children (node ?x1)) ?x1) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (= (children (leaf ?x1)) null) :rewrite-rule) ))


(declare-fun data (tree) nat)
(assert (forall ((?x1 nat))
                (! (= (data (leaf ?x1)) ?x1) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (= (data (node ?x1)) zero) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_node (tree) Bool)
(assert (forall ((?x1 list))
                (! (! (=> true (=> true (= (is_node (node ?x1)) true))) :pattern ((node ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 tree))
                (! (! (=> true (=> (is_node ?x1) (= ?x1 (node (children ?x1))))) :pattern ((children ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 tree))
                (! (! (=> true (=> (is_node ?x1) (= (data ?x1) zero))) :pattern ((data ?x1)) ) :rewrite-rule) ))


(declare-fun is_leaf (tree) Bool)
(assert (forall ((?x1 nat))
                (! (! (=> true (=> true (= (is_leaf (leaf ?x1)) true))) :pattern ((leaf ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 tree))
                (! (! (=> true (=> (is_leaf ?x1) (= ?x1 (leaf (data ?x1))))) :pattern ((data ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 tree))
                (! (! (=> true (=> (is_leaf ?x1) (= (children ?x1) null))) :pattern ((children ?x1)) ) :rewrite-rule) ))

;;; directrr
(assert (forall ((?x1 list))
                (! (= (is_node (node ?x1)) true) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (= (is_leaf (node ?x1)) false) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (= (is_leaf (leaf ?x1)) true) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (= (is_node (leaf ?x1)) false) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 tree))
                (! (=> (is_node ?x1) (not (is_leaf ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 tree))
                (! (=> (is_leaf ?x1) (not (is_node ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 tree))
                (! (=> (not (is_node ?x1)) (is_leaf ?x1) ) :rewrite-rule) ))
(assert (forall ((?x1 tree))
                (! (=> (not (is_leaf ?x1)) (is_node ?x1) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 tree))
                (! (! (=> true (or (is_node ?x1) (is_leaf ?x1))) :pattern ((children ?x1)) ) :rewrite-rule) ))

(assert (forall ((?x1 tree))
                (! (! (=> true (or (is_node ?x1) (is_leaf ?x1))) :pattern ((data ?x1)) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_list (list) Real)
(declare-fun size_tree (tree) Real)
(assert (forall ((?x1 tree) (?x2 list))
                (! (! (=> true (and (> (size_list (cons ?x1 ?x2)) (size_tree ?x1)) (> (size_list (cons ?x1 ?x2)) (size_list ?x2)))) :pattern ((cons ?x1 ?x2)) ) :rewrite-rule) ))
(assert (forall ((?x1 list))
                (! (! (=> true (> (size_tree (node ?x1)) (size_list ?x1))) :pattern ((node ?x1)) ) :rewrite-rule) ))
(assert (forall ((?x1 nat))
                (! (! (=> true (> (size_tree (leaf ?x1)) (size_nat ?x1))) :pattern ((leaf ?x1)) ) :rewrite-rule) ))
