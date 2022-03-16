(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)
(set-option :strings-exp true)
(set-option :re-elim true)
(declare-const actionName String)
(declare-const actionNamespace String)

; Action: p0.0
(declare-const p0.0.action Bool)
(assert (= p0.0.action (and (= actionNamespace "foobar") (str.in_re actionName (re.++ (str.to_re "foo") (re.* re.allchar) (re.++ (str.to_re "") re.allchar (str.to_re "bar")))))))

; Policy: 0
(declare-const p0.denies Bool)
(assert (not p0.denies))
(declare-const p0.allows Bool)
(assert (= p0.allows (and (not p0.denies) p0.0.action)))
(declare-const p0.neutral Bool)
(assert (= p0.neutral (and (not p0.allows) (not p0.denies))))

; Action: p1.0
(declare-const p1.0.action Bool)
(assert (= p1.0.action (and (= actionNamespace "foobar") (str.in_re actionName (re.++ (re.++ (str.to_re "foo") re.allchar (str.to_re "")) (re.* re.allchar) (str.to_re "bar"))))))

; Policy: 1
(declare-const p1.denies Bool)
(assert (not p1.denies))
(declare-const p1.allows Bool)
(assert (= p1.allows (and (not p1.denies) p1.0.action)))
(declare-const p1.neutral Bool)
(assert (= p1.neutral (and (not p1.allows) (not p1.denies))))

; Goals
(assert p0.allows)
(assert (or p1.denies p1.neutral))
(check-sat)
