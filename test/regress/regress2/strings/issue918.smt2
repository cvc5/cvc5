; COMMAND-LINE: --strings-exp --re-elim
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-option :produce-models true)
(set-logic UFDTSLIA)
(declare-datatypes () (
    (StringRotation (StringRotation$C_StringRotation (StringRotation$C_StringRotation$sr String)))
    (StringRotation2 (StringRotation2$C_StringRotation2 (StringRotation2$C_StringRotation2$sr1 StringRotation) (StringRotation2$C_StringRotation2$sr2 StringRotation)))
) )

(define-fun f1005$isValid_string((x$$1008 String)) Bool true)
(define-fun f1035$isValid_StringRotation((x$$1038 StringRotation)) Bool (and (f1005$isValid_string (StringRotation$C_StringRotation$sr x$$1038)) (or (or (or (= (StringRotation$C_StringRotation$sr x$$1038) "0 deg") (= (StringRotation$C_StringRotation$sr x$$1038) "90 deg")) (= (StringRotation$C_StringRotation$sr x$$1038) "180 deg")) (= (StringRotation$C_StringRotation$sr x$$1038) "270 deg"))))
(define-fun f1121$isValid_StringRotation2((x$$1124 StringRotation2)) Bool (and (f1035$isValid_StringRotation (StringRotation2$C_StringRotation2$sr1 x$$1124)) (f1035$isValid_StringRotation (StringRotation2$C_StringRotation2$sr2 x$$1124))))

(declare-fun $OutSR$1356$3$1$() StringRotation2)
(assert (f1121$isValid_StringRotation2 $OutSR$1356$3$1$))
(assert (and (is-StringRotation2$C_StringRotation2 $OutSR$1356$3$1$) (and (and 
(is-StringRotation$C_StringRotation (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) (or 

(str.in.re 
(StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) 
(re.++ (re.union (re.range "u" "~") (re.range " " "t") ) (re.union (re.range "K" "~") (re.range " " "J") ) (re.union (re.range "L" "~") (re.range " " "K") ) (re.union (re.range "y" "~") (re.range " " "x") ) (re.union (re.range "{" "~") (re.range " " "z") ) )
) 
(or 
(str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) 
(re.++ (re.union (re.range "s" "~") (re.range " " "r") ) (re.union (re.range "{" "~") (re.range " " "z") ) (re.union (re.range "u" "~") (re.range " " "t") ) ) )

(or 
(str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) (re.union (re.range "<" "~") (re.range " " ";") ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) (re.++ (re.union (re.range "&" "~") (re.range " " "%") ) (re.range " " "~") ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) (re.++ (re.union (re.range "`" "~") (re.range " " "_") ) (re.union (re.range "s" "~") (re.range " " "r") ) (re.union (re.range "1" "~") (re.range " " "0") ) (re.union (re.range "_" "~") (re.range " " "^") ) ) ) (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr1 $OutSR$1356$3$1$)) (re.* (re.union (re.range "\x00" "\x09") (re.range "\x0B" "\x0C") (re.range "\x0E" "\x7F") ) ) ))))))) (and (is-StringRotation$C_StringRotation (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.++ (re.union (re.range "<" "~") (re.range " " ";") ) (re.union (re.range "F" "~") (re.range " " "E") ) (re.union (re.range "u" "~") (re.range " " "t") ) (re.union (re.range "P" "~") (re.range " " "O") ) ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.union (re.range "E" "~") (re.range " " "D") ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.++ (re.union (re.range "x" "~") (re.range " " "w") ) (re.union (re.range "n" "~") (re.range " " "m") ) (re.union (re.range "d" "~") (re.range " " "c") ) (re.union (re.range "]" "~") (re.range " " "\\") ) (re.union (re.range "\\" "~") (re.range " " "[") ) ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.++ (re.union (re.range ":" "~") (re.range " " "9") ) (re.union (re.range "+" "~") (re.range " " "*") ) ) ) (or (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.++ (re.union (re.range "." "~") (re.range " " "-") ) (re.union (re.range "n" "~") (re.range " " "m") ) (re.union (re.range "|" "~") (re.range " " "{") ) ) ) (str.in.re (StringRotation$C_StringRotation$sr (StringRotation2$C_StringRotation2$sr2 $OutSR$1356$3$1$)) (re.* (re.union (re.range "\x00" "\x09") (re.range "\x0B" "\x0C") (re.range "\x0E" "\x7F") ) ) ))))))))))
(check-sat)
