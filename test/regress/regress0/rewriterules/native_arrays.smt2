;; This example can't be done if we don't access the EqualityEngine of
;; the theory of arrays

(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort Index 0)
(declare-sort Element 0)

;;A dumb predicate for a simple example
(declare-fun P (Element) Bool)

(assert-rewrite ((?i1 Index) (?i2 Index) (?e Element) (?a (Array Index Element))) () ()
                (P (select (store ?a ?i1 ?e) ?i2)) true )

(declare-fun a1 () (Array Index Element))
(declare-fun a2 () (Array Index Element))
(declare-fun a3 () (Array Index Element))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun e1 () Element)

(assert (not (=>  (or (= a1 (store a2 i1 e1)) (= a1 (store a3 i1 e1))) (P (select a1 i2)) )))
(check-sat)
(exit)


;; (declare-fun a1 () (Array Index Element))
;; (declare-fun a2 () (Array Index Element))
;; (declare-fun i1 () Index)
;; (assert (= (store a1 i1 (select a2 i1)) (store a2 i1 (select a1 i1))))
;; (assert (not (= a1 a2)))
;; (check-sat)
;; (exit)
