(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun v () String)

(declare-fun y () Int)

(assert (= 

(= v "Type") 

(str.contains 
  (str.++ (str.from_int (str.to_code (str.to_upper v))) (str.update "epyT" 1 (str.++ v v)))
  (str.from_int (+ 1 (str.indexof_re (str.replace_re_all v re.allchar v) re.none (str.to_int v)))))))


(check-sat)
