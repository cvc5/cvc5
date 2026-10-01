; EXPECT: unsat
(set-logic ALL)
(declare-const a String) 
(declare-const b String)  
(assert (> (mod 13 (str.len (str.++ (str.++ b (str.++ a "")) 
(str.++ (str.substr "" 13 (str.len (str.++ b (str.++ a (str.substr "" 13 
(str.len (str.++ b (str.++ a "")))))))) (str.substr "" 13 (str.len (str.++ b 
(str.++ a (str.substr "" 13 (str.len (str.++ b (str.++ a "")))))))))))) 
(mod 13 (str.len (str.++ (str.++ b (str.++ a "")) (str.++ (str.substr "" 13 
(str.len (str.++ b (str.++ a (str.substr "" 13 (str.len (str.++ b (str.++ a "")
))))))) (str.substr "" 13 (str.len (str.++ b (str.++ a (str.substr "" 13 
(str.len (str.++ b (str.++ a "")))))))))))))) 
(check-sat)
