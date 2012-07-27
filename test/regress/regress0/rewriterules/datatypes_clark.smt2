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
(assert-propagation((?x1 nat))
                 () () (= (inj1 (succ ?x1)) ?x1) (((succ ?x1))) )

;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun pred (nat) nat)
(assert-rewrite ((?x1 nat)) () (pred (succ ?x1)) ?x1 () )

(assert (= (pred zero) zero))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_succ (nat) Bool)
(assert (= (is_succ zero) false))
(assert-propagation ((?x1 nat)) () () (= (is_succ (succ ?x1)) true) (((succ ?x1))) )

(assert-propagation ((?x1 nat)) () ((is_succ ?x1)) (= ?x1 (succ (pred ?x1))) (((pred ?x1))))

(declare-fun is_zero (nat) Bool)
(assert (= (is_zero zero) true))
(assert-propagation ((?x1 nat)) () ((is_zero ?x1)) (= ?x1 zero) ())

;;; directrr
(assert-rewrite ((?x1 nat)) () (is_succ (succ ?x1)) true () )
(assert-rewrite ((?x1 nat)) () (is_zero (succ ?x1)) false () )


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert-propagation ((?x1 nat)) () ((is_zero ?x1)) (not (is_succ ?x1)) () )
(assert-propagation ((?x1 nat)) () ((is_succ ?x1)) (not (is_zero ?x1)) () )
(assert-propagation ((?x1 nat)) () ((not (is_zero ?x1))) (is_succ ?x1) () )
(assert-propagation ((?x1 nat)) () ((not (is_succ ?x1))) (is_zero ?x1) () )

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert-propagation ((?x1 nat)) () () (or (is_zero ?x1) (is_succ ?x1)) (((pred ?x1))) )

;;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_nat (nat) Real)
(assert-propagation ((?x1 nat)) () () (> (size_nat (succ ?x1)) (size_nat ?x1)) (((succ ?x1))) )



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
(assert-propagation ((?x1 tree) (?x2 list)) () () (= (inj2 (cons ?x1 ?x2)) ?x1) (((cons ?x1 ?x2))) )

(declare-fun inj3 (list) list)
(assert-propagation ((?x1 tree) (?x2 list)) () () (= (inj3 (cons ?x1 ?x2)) ?x2) (((cons ?x1 ?x2))) )


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun car (list) tree)
(assert-rewrite ((?x1 tree) (?x2 list)) () (car (cons ?x1 ?x2)) ?x1 ())

(assert (= (car null) (node null)))

(declare-fun cdr (list) list)
(assert-rewrite ((?x1 tree) (?x2 list)) () (cdr (cons ?x1 ?x2)) ?x2 ())

(assert (= (cdr null) null))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_cons (list) Bool)
(assert (= (is_cons null) false))
(assert-propagation ((?x1 tree) (?x2 list)) () () (= (is_cons (cons ?x1 ?x2)) true) (((cons ?x1 ?x2))) )

(assert-propagation ((?x1 list)) () ((is_cons ?x1)) (= ?x1 (cons (car ?x1) (cdr ?x1))) (((car ?x1))) )
(assert-propagation ((?x1 list)) () ((is_cons ?x1)) (= ?x1 (cons (car ?x1) (cdr ?x1))) (((cdr ?x1))) )

(declare-fun is_null (list) Bool)
(assert (= (is_null null) true))

(assert-propagation ((?x1 list)) () ((is_null ?x1)) (= (car ?x1) (node null)) (((car ?x1))) )
(assert-propagation ((?x1 list)) () ((is_null ?x1)) (= (cdr ?x1) null) (((cdr ?x1))) )

(assert-propagation ((?x1 list)) () ((is_null ?x1)) (= ?x1 null) ())

;;; directrr
(assert-rewrite ((?x1 tree) (?x2 list)) () (is_cons (cons ?x1 ?x2)) true ())
(assert-rewrite ((?x1 tree) (?x2 list)) () (is_null (cons ?x1 ?x2)) false ())



;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert-propagation ((?x1 list)) () ((is_null ?x1)) (not (is_cons ?x1)) () )
(assert-propagation ((?x1 list)) () ((is_cons ?x1)) (not (is_null ?x1)) () )
(assert-propagation ((?x1 list)) () ((not (is_null ?x1))) (is_cons ?x1) () )
(assert-propagation ((?x1 list)) () ((not (is_cons ?x1))) (is_null ?x1) () )

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert-propagation ((?x1 list)) () () (or (is_null ?x1) (is_cons ?x1)) (((car ?x1))) )
(assert-propagation ((?x1 list)) () () (or (is_null ?x1) (is_cons ?x1)) (((cdr ?x1))) )

;;;;;;;;;;;;;;;
;; tree

;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj4 (tree) list)
(assert-propagation ((?x1 list)) () () (= (inj4 (node ?x1)) ?x1) (((node ?x1))) )

(declare-fun inj5 (tree) nat)
(assert-propagation ((?x1 nat)) () () (= (inj5 (leaf ?x1)) ?x1) (((leaf ?x1))) )


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun children (tree) list)
(assert-rewrite ((?x1 list)) () (children (node ?x1)) ?x1 () )
(assert-rewrite ((?x1 nat)) () (children (leaf ?x1)) null () )

(declare-fun data (tree) nat)
(assert-rewrite ((?x1 nat)) () (data (leaf ?x1)) ?x1 () )
(assert-rewrite ((?x1 list)) () (data (node ?x1)) zero () )

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun is_node (tree) Bool)
(assert-propagation ((?x1 list)) () () (= (is_node (node ?x1)) true) (((node ?x1))) )

(assert-propagation ((?x1 tree)) () ((is_node ?x1)) (= ?x1 (node (children ?x1))) (((children ?x1))) )
(assert-propagation ((?x1 tree)) () ((is_node ?x1)) (= (data ?x1) zero) (((data ?x1))) )


(declare-fun is_leaf (tree) Bool)
(assert-propagation ((?x1 nat)) () () (= (is_leaf (leaf ?x1)) true) (((leaf ?x1))) )
(assert-propagation ((?x1 tree)) () ((is_leaf ?x1)) (= ?x1 (leaf (data ?x1))) (((data ?x1))) )
(assert-propagation ((?x1 tree)) () ((is_leaf ?x1)) (= (children ?x1) null) (((children ?x1))) )

;;; directrr
(assert-rewrite ((?x1 list)) () (is_node (node ?x1)) true () )
(assert-rewrite ((?x1 list)) () (is_leaf (node ?x1)) false () )
(assert-rewrite ((?x1 nat)) () (is_leaf (leaf ?x1)) true () )
(assert-rewrite ((?x1 nat)) () (is_node (leaf ?x1)) false () )


;;;;;;;;;;;;;;;;;;;;
;; distinct
(assert-propagation ((?x1 tree)) () ((is_node ?x1)) (not (is_leaf ?x1)) () )
(assert-propagation ((?x1 tree)) () ((is_leaf ?x1)) (not (is_node ?x1)) () )
(assert-propagation ((?x1 tree)) () ((not (is_node ?x1))) (is_leaf ?x1) () )
(assert-propagation ((?x1 tree)) () ((not (is_leaf ?x1))) (is_node ?x1) () )

;;;;;;;;;;;;;;;;;;;
;; case-split
(assert-propagation ((?x1 tree)) () () (or (is_node ?x1) (is_leaf ?x1)) (((children ?x1))) )
(assert-propagation ((?x1 tree)) () () (or (is_node ?x1) (is_leaf ?x1)) (((data ?x1))) )


;;;;;;;;;;;;;;;;;;
;; non-cyclic
(declare-fun size_list (list) Real)
(declare-fun size_tree (tree) Real)
(assert-propagation ((?x1 tree) (?x2 list)) () () (and (> (size_list (cons ?x1 ?x2)) (size_tree ?x1)) (> (size_list (cons ?x1 ?x2)) (size_list ?x2))) (((cons ?x1 ?x2))) )
(assert-propagation ((?x1 list)) () () (> (size_tree (node ?x1)) (size_list ?x1)) (((node ?x1))) )
(assert-propagation ((?x1 nat)) () () (> (size_tree (leaf ?x1)) (size_nat ?x1)) (((leaf ?x1))) )
