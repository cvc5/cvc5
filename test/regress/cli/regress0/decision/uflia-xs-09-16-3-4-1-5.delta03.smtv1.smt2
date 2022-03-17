; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-option :incremental false)
(set-info :status sat)
(set-logic QF_UFLIA)
(declare-fun fmt_length () Int)
(declare-fun fmt1 () Int)
(declare-fun arg1 () Int)
(declare-fun select_format (Int) Int)
(check-sat-assuming ( (and (and (= 1 (select_format (+ 1 fmt1))) (= (select_format arg1) 0)) (and (or (= 1 (select_format 7)) (or (or (or (= 1 (select_format 0)) (= 1 (select_format 1))) (= 0 (select_format 5))) (= 0 (select_format 6)))) (and (= 9 fmt_length) (and (= arg1 (- fmt1 2)) (< fmt1 fmt_length))))) ))
