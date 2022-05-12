(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)
(set-option :strings-exp true)
(set-option :re-elim on)
(declare-const actionName String)
(declare-const actionNamespace String)
(declare-const example_key String)

; Action: p0.0
(declare-const p0.0.action Bool)
(assert (= p0.0.action (and (= "foobar" actionNamespace) (and (str.prefixof "ab" actionName) (str.contains (str.substr actionName 2 (- (str.len actionName) 3)) "b") (str.suffixof "b" actionName) (not (= actionName "abb")) (not (= actionName "ab"))))))

; Policy: 0
(declare-const p0.denies Bool)
(assert (not p0.denies))
(declare-const p0.allows Bool)
(assert (= p0.allows (and (not p0.denies) p0.0.action)))
(declare-const p0.neutral Bool)
(assert (= p0.neutral (and (not p0.allows) (not p0.denies))))

; Action: p1.0
(declare-const p1.0.action Bool)
(assert (= p1.0.action (and (= "foobar" actionNamespace) (and (str.prefixof "a" actionName) (str.prefixof example_key (str.substr actionName 1 (- (str.len actionName) 1))) (str.contains (str.substr actionName (+ 1 (str.len example_key)) (- (str.len actionName) 1 (str.len example_key))) "b") (str.suffixof "b" actionName)))))

(declare-const p1.0.condition Bool)
(assert (= p1.0.condition (str.prefixof "bb" example_key)))

; Policy: 1
(declare-const p1.denies Bool)
(assert (not p1.denies))
(declare-const p1.allows Bool)
(assert (= p1.allows (and (not p1.denies) p1.0.action p1.0.condition)))
(declare-const p1.neutral Bool)
(assert (= p1.neutral (and (not p1.allows) (not p1.denies))))

; Goals
(assert (or p0.neutral p0.denies))
(assert p1.allows)
(check-sat)
