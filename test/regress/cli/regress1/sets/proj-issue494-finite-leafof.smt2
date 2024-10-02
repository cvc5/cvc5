(set-logic ALL)
(set-info :status unsat)
(set-option :strings-exp true)
(set-option :sets-exp true)
(declare-const x (Array (Set RoundingMode) (Set RoundingMode)))
(check-sat-assuming (
(seq.nth 
(seq.++ (seq.++ (seq.unit false) (seq.unit false)) (seq.++ (seq.unit false) (seq.unit false)) (seq.++ (seq.unit false) (seq.unit false))) 
(set.card (select x (as set.universe (Set RoundingMode)))))))
