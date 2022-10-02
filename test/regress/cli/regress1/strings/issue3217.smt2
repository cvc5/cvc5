(set-logic ALL)
(set-option :strings-exp true)
(set-info :status unsat)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert 
    (or 
        (not (= ( str.suffixof "B" ( str.replace "A" b "B")) (= ( str.substr a 0 (str.len b)) "A"))) 
        (not (= (not (= c "A")) ( str.suffixof "A" ( str.replace "A" c "B"))))))
(assert (= a (str.++ (str.++ b "") d)))
(check-sat)
