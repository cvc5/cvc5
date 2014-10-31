(set-logic QF_ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :status unknown)

(declare-fun text () String)
(declare-fun output () String)

; html_escape_table = {
;    "&": "&amp;",
;    '"': "&quot;",
;    "'": "&apos;",
;    ">": "&gt;",
;    "<": "&lt;",
;    }
(declare-fun html_escape_table () (Array String String))
(assert (= html_escape_table 
    (store (store (store (store (store ((as const (Array String String)) "A") 
    "&" "&amp;") 
    "\"" "&quot;")
    "'" "&apos;") 
    ">" "&gt;") 
    "<" "&lt;")))
(declare-fun html_escape_table_keys () (Array Int String))
(assert (= html_escape_table_keys
    (store (store (store (store (store ((as const (Array Int String)) "B")
    0 "&")
    1 "\"")
    2 "'")
    3 ">")
    4 "<"))) 

; charlst = [c for c in text]
(declare-fun charlst () (Array Int String))
(declare-fun charlstlen () Int)
(assert (= charlstlen (str.len text)))
(assert (forall ((i Int))
    (= (select charlst i) (str.at text i))
))

; charlst2 = [html_escape_table.get(c, c) for c in charlst]
(declare-fun charlst2 () (Array Int String))
(declare-fun charlstlen2 () Int)
(assert (= charlstlen2 charlstlen))
(assert (forall ((i Int))
    (or (or (< i 0) (>= i charlstlen2))
        (and (exists ((j Int))
               (= (select html_escape_table_keys j) (select charlst i))
            )
            (= (select charlst2 i) (select html_escape_table (select charlst i)))         
        )
        (and (not (exists ((j Int))
                (= (select html_escape_table_keys j) (select charlst i))
            ))
            (= (select charlst2 i) (select charlst i))
        )                        
    )
))
(check-sat)
(get-value (charlst2))
