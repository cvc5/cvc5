(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun a () String)
(declare-fun b () String)
(assert
 (str.in_re (str.++ a "C" b)
  (re.*
   (re.++ (re.union (str.to_re "A") (str.to_re "B"))
    (re.*
     (re.++ (re.union (str.to_re "A") (str.to_re "B"))
      (re.* (str.to_re "A"))
      (re.union (str.to_re "B") (str.to_re "C"))))
    (re.union (str.to_re "B") (str.to_re "C"))))))
(check-sat)
