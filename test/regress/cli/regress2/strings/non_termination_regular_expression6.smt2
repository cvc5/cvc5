; COMMAND-LINE: --strings-exp --re-elim=on
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-const actionName String)
(declare-const actionNamespace String)
(declare-const resource_account String)
(declare-const resource_partition String)
(declare-const resource_prefix String)
(declare-const resource_region String)
(declare-const resource_resource String)
(declare-const resource_service String)

; Action: p0.0
(declare-const p0.0.action Bool)
(assert (= p0.0.action (and (= "sqs" actionNamespace) (= "sendmessage" actionName))))

; Resource: p0.0
(declare-const p0.0.resource Bool)
(assert (= p0.0.resource (and (= resource_prefix "arn") (= resource_partition "aws") (= resource_service "sqs") (= resource_region "us-east-1") (= resource_account "111144448888") (str.in_re resource_resource (re.++ (str.to_re "ab") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b"))))))

; Statement: p0.0
(declare-const p0.0.statement.allows Bool)
(assert (= p0.0.statement.allows (and p0.0.action p0.0.resource)))

; Policy: 0
(declare-const p0.denies Bool)
(assert (not p0.denies))
(declare-const p0.allows Bool)
(assert (= p0.allows (and (not p0.denies) p0.0.statement.allows)))
(declare-const p0.neutral Bool)
(assert (= p0.neutral (and (not p0.allows) (not p0.denies))))

; Action: p1.0
(declare-const p1.0.action Bool)
(assert (= p1.0.action (and (= "sqs" actionNamespace) (= "sendmessage" actionName))))

; Resource: p1.0
(declare-const p1.0.resource Bool)
(assert (= p1.0.resource (and (= resource_prefix "arn") (= resource_partition "aws") (= resource_service "sqs") (= resource_region "us-east-1") (= resource_account "111144448888") (str.in_re resource_resource (re.++ (str.to_re "a") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b"))))))

; Statement: p1.0
(declare-const p1.0.statement.allows Bool)
(assert (= p1.0.statement.allows (and p1.0.action p1.0.resource)))

; Policy: 1
(declare-const p1.denies Bool)
(assert (not p1.denies))
(declare-const p1.allows Bool)
(assert (= p1.allows (and (not p1.denies) p1.0.statement.allows)))
(declare-const p1.neutral Bool)
(assert (= p1.neutral (and (not p1.allows) (not p1.denies))))

; Resource service invariant
(assert (not (str.contains resource_service ":")))
(assert (= resource_prefix "arn"))

; Goals
(assert p0.allows)
(assert (or p1.denies p1.neutral))
(check-sat)
