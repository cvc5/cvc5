(set-logic ALL)
(set-info :status unsat)
(set-option :strings-exp true)

(declare-fun url () String)

(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (not (= (ite (> (str.indexof url ":" 0) 0) 1 0) 0))) (not (= (ite (str.contains url "javascript:alert(1);") 1 0) 0))) (not (not (= (ite (= (str.len url) 0) 1 0) 0)))) (not (not (= (ite (= (str.at url 0) " ") 1 0) 0)))) (not (not (= (ite (= (str.at url 0) "\t") 1 0) 0)))) (not (not (= (ite (= (str.at url 0) "\n") 1 0) 0)))) (not (not (= (ite (= (str.at url 0) "\r") 1 0) 0)))) (not (not (= (ite (= (str.at url 0) "\v") 1 0) 0)))) (not (not (= (ite (= (str.at url 0) "\f") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) " ") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) "\t") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) "\n") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) "\r") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) "\v") 1 0) 0)))) (not (not (= (ite (= (str.at url (- (str.len url) 1)) "\f") 1 0) 0)))) (not (= (ite (str.prefixof "javascript:alert(1);" url) 1 0) 0))))

(check-sat)
