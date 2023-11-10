; COMMAND-LINE: --user-pat=strict
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(set-info :status unsat)

(define-sort I () Int)
;(declare-sort E 0)
(define-sort E () Int)
(declare-sort Arr 0)
(declare-fun arr.select (Arr I) E)
(declare-fun arr.store (Arr I E) Arr)

(declare-const w Int)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const k Int)
(declare-const l Int)
(declare-const n Int)
(declare-const a Arr)

(declare-pool Index I (0 (- n 1)))

(assert 
(forall ((a Arr) (i I) (e E)) (! 
  (and (= (arr.select (arr.store a i e) i) e) 
       (forall ((j I)) (!
       (=> (not (= i j)) (= (arr.select a j) (arr.select (arr.store a i e) j)))
       :pool (Index)
       )
       ))
  :pattern ((arr.store a i e))
  :inst-add-to-pool ((- i 1) Index)
  :inst-add-to-pool ((+ i 1) Index)
  :inst-add-to-pool (i Index)
))
)

(define-fun sorted ((l I) (u I) (a Arr)) Bool 
  (forall ((i I) (j I)) (!
    (=> 
      (<= l i j u) 
      (<= (arr.select a i) (arr.select a j)))
    :pool (Index Index))
  ))


(assert (< w x y z))
(assert (< 0 k l n))
(assert (> (- l k) 1))
(assert (sorted 0 (- n 1) (arr.store (arr.store a k x) l w)))
(assert (sorted 0 (- n 1) (arr.store (arr.store a k y) l z)))

(check-sat)
