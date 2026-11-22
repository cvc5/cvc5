; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --check-models
; The ite in the body of the first lambda is ground, so it is purified to a
; skolem k with the definition (= (ite ..) k), which ite removal then
; rewrites to true, and ite removal adds the definition of k. Registering
; true as the definition of k hid the second one from the justification
; heuristic: k was unconstrained, and the model of q failed the model check.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const t (Bag (Tuple (Nullable Int))))
(declare-fun q ((Nullable String) (Nullable String)) (Nullable Bool))
(assert (not (= (bag.map (lambda ((x (Tuple (Nullable Int))))
                           (let ((c (q (nullable.some "a") (nullable.some "B"))))
                             (tuple (ite (and (nullable.is_some c) (nullable.val c))
                                         (nullable.some 1)
                                         (nullable.some 0)))))
                         t)
                (bag.map (lambda ((x (Tuple (Nullable Int)))) (tuple (nullable.some 0))) t))))
(check-sat)
