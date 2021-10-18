; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-logic UF)
(set-option :produce-abducts true)
(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(assert (=> A C))
(get-abduct D (=> A B))
