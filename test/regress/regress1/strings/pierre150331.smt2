(set-info :smt-lib-version 2.6)
(set-logic SLIA)
(set-info :status sat)
(set-option :strings-exp true)
(define-fun stringEval ((?s String)) Bool (str.in_re ?s 
(re.union 
(str.to_re "H")
(re.++ ((_ re.loop 2 2) (str.to_re "{") ) ((_ re.loop 2 4) (re.union re.none (re.range "\u{1d}" "]") (re.range "\u{e}" "^") ) ) ) ) ) )
(declare-fun s0() String)
(declare-fun s1() String)
(declare-fun s2() String)
(assert (and true (stringEval s0) (stringEval s1) (distinct s0 s1) (stringEval s2) (distinct s0 s2) (distinct s1 s2) ) )
(check-sat)
