; EXPECT: unsat
;; Unsat core checking with proofs, which at one point had issues for this
;; benchmark due to cycle detection in LazyCDProofChain
(set-logic ALL)
(set-info :status unsat)
(set-option :check-unsat-cores true)
(declare-fun i8 () Int)
(declare-fun st6 () (Set String))
(declare-fun st8 () (Set String))
(declare-fun str6 () String)
(declare-fun str7 () String)
(assert (= 0 (set.card st8)))
(assert (str.in_re str6 (re.opt re.none)))
(assert (str.in_re (str.substr str7 0 i8) re.allchar))
(assert (xor true (set.subset st8 st6) (not (= str7 str6)) true))
(check-sat)
