(set-info :smt-lib-version 2.6)
(set-logic ASLIA)
(set-option :strings-exp true)
(set-info :status sat)

; regex = [\*-,\t\*-\|](.{6,}()?)+
(define-fun strinre ((?s String)) Bool (str.in_re ?s (re.union re.none (re.++ (str.to_re "") (str.to_re "") (re.union re.none (re.range "*" ",") (str.to_re "\t") (re.range "*" "|") ) (re.+ (re.union re.none (re.++ (str.to_re "") (str.to_re "") ((_ re.^ 6) re.allchar) (re.opt (re.union re.none (re.++ (str.to_re "") (str.to_re "") ) ) ) ) ) ) ) )  ) )
(assert (not (strinre "6O\1\127\n?")))

(check-sat)
