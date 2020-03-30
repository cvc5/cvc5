(set-info :smt-lib-version 2.5)
(set-logic SLIA)
(set-info :status sat)
(set-info :smt-lib-version 2.5)
(set-option :strings-exp true)
(define-fun stringEval ((?s String)) Bool (str.in.re ?s 
(re.union 
(str.to.re "H")
(re.++ ((_ re.loop 2 2) (str.to.re "{") ) ((_ re.loop 2 4) (re.union re.nostr (re.range "" "]") (re.range "" "^") ) ) ) ) ) )
(declare-fun s0() String)
(declare-fun s1() String)
(declare-fun s2() String)
(assert (and true (stringEval s0) (stringEval s1) (distinct s0 s1) (stringEval s2) (distinct s0 s2) (distinct s1 s2) ) )
(check-sat)
