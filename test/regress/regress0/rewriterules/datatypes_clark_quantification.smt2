(set-logic AUFLIRA)

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
                (! (= (inj1 (succ ?x1)) ?x1) :pattern ((succ ?x1)) ) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun pred (nat) nat)
(assert (forall ((?x1 nat))
                (! (= (pred (succ ?x1)) ?x1) :pattern ((pred (succ ?x1))) ) ))

(assert (= (pred zero) zero))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_succ (nat) Bool)
(assert (= (is_succ zero) false))
(assert (forall ((?x1 nat))
                (! (= (is_succ (succ ?x1)) true) :pattern ((succ ?x1)) ) ))

(assert (forall ((?x1 nat))
                (! (=> (is_succ ?x1) (= ?x1 (succ (pred ?x1)))) :pattern ((is_succ ?x1) (pred ?x1)) ) ))

(declare-fun is_zero (nat) Bool)
(assert (= (is_zero zero) true))
(assert (forall ((?x1 nat))
                (! (=> (is_zero ?x1) (= ?x1 zero)) :pattern ((is_zero ?x1)) ) ))

;;; directrr
(assert (forall ((?x1 nat))
                (! (= (is_succ (succ ?x1)) true) :pattern ((is_succ (succ ?x1))) ) ))
(assert (forall ((?x1 nat))
                (! (= (is_zero (succ ?x1)) false) :pattern ((is_zero (succ ?x1))) )))


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 nat))
                (! (=> (is_zero ?x1) (not (is_succ ?x1)) ) :pattern ((is_zero ?x1)) ) ))
(assert (forall ((?x1 nat))
                (! (=> (is_succ ?x1) (not (is_zero ?x1)) ) :pattern ((is_succ ?x1)) ) ))
(assert (forall ((?x1 nat))
                (! (=> (not (is_zero ?x1)) (is_succ ?x1) ) :pattern ((is_zero ?x1)) ) ))
(assert (forall ((?x1 nat))
                (! (=> (not (is_succ ?x1)) (is_zero ?x1) ) :pattern ((is_succ ?x1)) ) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 nat))
                (! (or (is_zero ?x1) (is_succ ?x1)) :pattern ((pred ?x1)) ) ))

;;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_nat (nat) Real)
(assert (forall ((?x1 nat))
                (! (> (size_nat (succ ?x1)) (size_nat ?x1)) :pattern ((succ ?x1)) ) ))



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
                (! (= (inj2 (cons ?x1 ?x2)) ?x1) :pattern ((cons ?x1 ?x2)) ) ))

(declare-fun inj3 (list) list)
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (inj3 (cons ?x1 ?x2)) ?x2) :pattern ((cons ?x1 ?x2)) ) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun car (list) tree)
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (car (cons ?x1 ?x2)) ?x1) :pattern ((car (cons ?x1 ?x2))) ) ))

(assert (= (car null) (node null)))

(declare-fun cdr (list) list)
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (cdr (cons ?x1 ?x2)) ?x2) :pattern ((cdr (cons ?x1 ?x2))) ) ))

(assert (= (cdr null) null))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_cons (list) Bool)
(assert (= (is_cons null) false))
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (is_cons (cons ?x1 ?x2)) true) :pattern ((cons ?x1 ?x2)) ) ))

(assert (forall ((?x1 list))
                (! (=> (is_cons ?x1) (= ?x1 (cons (car ?x1) (cdr ?x1)))) :pattern ((is_cons ?x1)(car ?x1)) ) ))
(assert (forall ((?x1 list))
                (! (=> (is_cons ?x1) (= ?x1 (cons (car ?x1) (cdr ?x1)))) :pattern ((is_cons ?x1)(cdr ?x1)) ) ))

(declare-fun is_null (list) Bool)
(assert (= (is_null null) true))

(assert (forall ((?x1 list))
                (! (=> (is_null ?x1) (= (car ?x1) (node null))) :pattern ((is_null ?x1)(car ?x1)) )  ))
(assert (forall ((?x1 list))
                (! (=> (is_null ?x1) (= (cdr ?x1) null)) :pattern ((is_null ?x1)(cdr ?x1)) ) ))

(assert (forall ((?x1 list))
                (! (=> (is_null ?x1) (= ?x1 null)) :pattern ((is_null ?x1)) ) ))

;;; directrr
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (is_cons (cons ?x1 ?x2)) true) :pattern ((is_cons (cons ?x1 ?x2))) ) ))
(assert (forall ((?x1 tree) (?x2 list))
                (! (= (is_null (cons ?x1 ?x2)) false) :pattern ((is_null (cons ?x1 ?x2))) ) ))



;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 list))
                (! (=> (is_null ?x1) (not (is_cons ?x1)) ) :pattern ((is_null ?x1)) ) ))
(assert (forall ((?x1 list))
                (! (=> (is_cons ?x1) (not (is_null ?x1)) ) :pattern ((is_cons ?x1)) ) ))
(assert (forall ((?x1 list))
                (! (=> (not (is_null ?x1)) (is_cons ?x1) ) :pattern ((is_null ?x1)) ) ))
(assert (forall ((?x1 list))
                (! (=> (not (is_cons ?x1)) (is_null ?x1) ) :pattern ((is_cons ?x1)) ) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 list))
            (!  (or (is_null ?x1) (is_cons ?x1)) :pattern ((car ?x1)) ) ))
(assert (forall ((?x1 list))
            (! (or (is_null ?x1) (is_cons ?x1)) :pattern ((cdr ?x1)) ) ))

;;;;;;;;;;;;;;;
;; tree

;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj4 (tree) list)
(assert (forall ((?x1 list))
                (! (= (inj4 (node ?x1)) ?x1) :pattern ((node ?x1)) ) ))

(declare-fun inj5 (tree) nat)
(assert (forall ((?x1 nat))
                (!  (= (inj5 (leaf ?x1)) ?x1) :pattern ((leaf ?x1)) )  ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun children (tree) list)
(assert (forall ((?x1 list))
                (! (= (children (node ?x1)) ?x1) :pattern ((children (node ?x1))) ) ))
(assert (forall ((?x1 nat))
                (! (= (children (leaf ?x1)) null) :pattern ((children (leaf ?x1))) ) ))


(declare-fun data (tree) nat)
(assert (forall ((?x1 nat))
                (! (= (data (leaf ?x1)) ?x1) :pattern ((data (leaf ?x1))) ) ))
(assert (forall ((?x1 list))
                (! (= (data (node ?x1)) zero) :pattern ((data (node ?x1))) ) ))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_node (tree) Bool)
(assert (forall ((?x1 list))
                (! (= (is_node (node ?x1)) true) :pattern ((node ?x1)) )  ))

(assert (forall ((?x1 tree))
                (! (=> (is_node ?x1) (= ?x1 (node (children ?x1)))) :pattern ((is_node ?x1)(children ?x1)) ) ))

(assert (forall ((?x1 tree))
                (! (=> (is_node ?x1) (= (data ?x1) zero)) :pattern ((is_node ?x1)(data ?x1)) ) ))


(declare-fun is_leaf (tree) Bool)
(assert (forall ((?x1 nat))
                (! (=> true (= (is_leaf (leaf ?x1)) true)) :pattern ((leaf ?x1)) ) ))

(assert (forall ((?x1 tree))
                (! (=> (is_leaf ?x1) (= ?x1 (leaf (data ?x1)))) :pattern ((is_leaf ?x1)(data ?x1)) ) ))
(assert (forall ((?x1 tree))
                (! (=> (is_leaf ?x1) (= (children ?x1) null)) :pattern ((is_leaf ?x1)(children ?x1)) ) ))

;;; directrr
(assert (forall ((?x1 list))
                (! (= (is_node (node ?x1)) true) :pattern ((is_node (node ?x1))) ) ))
(assert (forall ((?x1 list))
                (! (= (is_leaf (node ?x1)) false) :pattern ((is_leaf (node ?x1))) ) ))
(assert (forall ((?x1 nat))
                (! (= (is_leaf (leaf ?x1)) true) :pattern (is_leaf (leaf ?x1)) ) ))
(assert (forall ((?x1 nat))
                (! (= (is_node (leaf ?x1)) false) :pattern ((is_node (leaf ?x1))) ) ))


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert (forall ((?x1 tree))
                (! (=> (is_node ?x1) (not (is_leaf ?x1)) ) :pattern ((is_node ?x1)) ) ))
(assert (forall ((?x1 tree))
                (! (=> (is_leaf ?x1) (not (is_node ?x1)) ) :pattern ((is_leaf ?x1)) ) ))
(assert (forall ((?x1 tree))
                (! (=> (not (is_node ?x1)) (is_leaf ?x1) ) :pattern ((is_node ?x1)) ) ))
(assert (forall ((?x1 tree))
                (! (=> (not (is_leaf ?x1)) (is_node ?x1) ) :pattern ((is_leaf ?x1)) ) ))

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?x1 tree))
                (!  (or (is_node ?x1) (is_leaf ?x1)) :pattern ((children ?x1)) ) ))

(assert (forall ((?x1 tree))
                (! (or (is_node ?x1) (is_leaf ?x1)) :pattern ((data ?x1)) )  ))


;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_list (list) Real)
(declare-fun size_tree (tree) Real)
(assert (forall ((?x1 tree) (?x2 list))
                (! (and (> (size_list (cons ?x1 ?x2)) (size_tree ?x1)) (> (size_list (cons ?x1 ?x2)) (size_list ?x2))) :pattern ((cons ?x1 ?x2)) ) ))
(assert (forall ((?x1 list))
                (! (> (size_tree (node ?x1)) (size_list ?x1)) :pattern ((node ?x1)) )  ))
(assert (forall ((?x1 nat))
                (! (> (size_tree (leaf ?x1)) (size_nat ?x1)) :pattern ((leaf ?x1)) ) ))
