; COMMAND-LINE:  --uf-ho --finite-model-find --no-check-models
; EXPECT: sat


(set-logic ALL)
(declare-sort $$unsorted 0)

(declare-fun mvalid ((-> $$unsorted Bool)) Bool)
(assert (= mvalid (lambda ((Phi (-> $$unsorted Bool))) (forall ((W $$unsorted)) (Phi W) ))))

(declare-fun mforall_prop ((-> (-> $$unsorted Bool) $$unsorted Bool) $$unsorted) Bool)
(assert (= mforall_prop
          (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
            (forall ((P (-> $$unsorted Bool))) (Phi P W) ))))

(declare-fun mnot ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mnot (lambda ((Phi (-> $$unsorted Bool)) (W $$unsorted)) (not (Phi W)))))

(declare-fun mor ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mor
          (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (W $$unsorted))
            (or (Phi W) (Psi W)))))

(declare-fun mimplies ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mimplies
          (lambda (
                    (Phi (-> $$unsorted Bool))
                    (Psi (-> $$unsorted Bool)) (__flatten_var_0 $$unsorted))
            (mor (mnot Phi) Psi __flatten_var_0))))

(define-fun mbox () (-> (-> $$unsorted $$unsorted Bool) (-> $$unsorted Bool) $$unsorted Bool)
          (lambda ((R (-> $$unsorted $$unsorted Bool)) (Phi (-> $$unsorted Bool)) (W $$unsorted))
            (forall ((V $$unsorted)) (or (not (R W V)) (Phi V)) )))

(assert (not (forall ((R (-> $$unsorted $$unsorted Bool)))
               (mvalid
                 (mforall_prop
                   (lambda ((A (-> $$unsorted Bool)) (__flatten_var_0 $$unsorted))
                     (mforall_prop
                       (lambda ((B (-> $$unsorted Bool)) (__flatten_var_0 $$unsorted))
                         (mimplies
                           (mbox R (mor A B))
                           (mor
                             (mbox R A)
                             (mbox R B))
                           __flatten_var_0))
                       __flatten_var_0)))) )))

(check-sat)
