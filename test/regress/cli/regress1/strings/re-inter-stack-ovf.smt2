(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun var0 () String)
(assert (str.in_re var0 

(re.++ 
  (re.+ (re.union (re.* (re.union (re.+ (re.* (re.union (re.+ (re.* (str.to_re "0"))) (re.+ (re.+ (str.to_re "111")))))) (re.union (re.+ (re.* (re.* (re.+ (str.to_re "22"))))) (re.union (re.union (re.union (re.union (str.to_re "333") (str.to_re "4")) (re.* (str.to_re "55"))) (re.* (re.+ (str.to_re "66")))) (re.+ (re.+ (re.+ (str.to_re "7")))))))) (re.* (re.+ (re.+ (re.* (re.union (re.union (re.union (str.to_re "88") (str.to_re "999")) (re.* (str.to_re "aaa"))) (re.* (re.* (str.to_re "bb")))))))))) 
  (re.+ (re.* (re.union (re.* (re.union (re.* (re.+ (re.+ (re.union (str.to_re "ccc") (str.to_re "dd"))))) (re.* (re.+ (re.* (re.+ (str.to_re "ee"))))))) (re.* (re.+ (re.+ (re.union (re.+ (re.+ (str.to_re "ff"))) (re.union (re.* (str.to_re "g")) (re.+ (str.to_re "hhh")))))))))))
))
(assert (<= 15 (str.len var0)))
(check-sat)
