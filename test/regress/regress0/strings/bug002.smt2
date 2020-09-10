(set-info :smt-lib-version 2.0)
(set-logic ASLIA)
(set-option :strings-exp true)
(set-info :status sat)

; regex = [\*-,\t\*-\|](.{6,}()?)+
(define-fun strinre ((?s String)) Bool (str.in.re ?s (re.union re.nostr (re.++ (str.to.re "") (str.to.re "") (re.union re.nostr (re.range "*" ",") (str.to.re "\t") (re.range "*" "|") ) (re.+ (re.union re.nostr (re.++ (str.to.re "") (str.to.re "") ((_ re.^ 6) re.allchar) (re.opt (re.union re.nostr (re.++ (str.to.re "") (str.to.re "") ) ) ) ) ) ) ) )  ) )
(assert (not (strinre "6O\1\127\n?")))

(check-sat)
