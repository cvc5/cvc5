(set-logic ALL_SUPPORTED)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun url () String)

(assert 
(and 
(and 
(and 
(and 

(= (str.len (str.substr (str.substr url (str.indexof url "#" 2) (- (str.len url) (str.indexof url "#" 2))) (+ (str.indexof (str.substr url (str.indexof url "#" 2) (- (str.len url) (str.indexof url "#" 2))) "#" 0) 1) (- (str.len (str.substr url (str.indexof url "#" 2) (- (str.len url) (str.indexof url "#" 2)))) (+ (str.indexof (str.substr url (str.indexof url "#" 2) (- (str.len url) (str.indexof url "#" 2))) "#" 0) 1)))) 0) 

(not (= (str.substr url 0 (- (str.indexof url ":" 0) 0)) "http")))
(> (str.indexof url ":" 0) 0))
(>= (- (str.indexof url "#" 2) 2) 0)) 
(>= (str.indexof url ":" 0) 0))
)

(check-sat)

