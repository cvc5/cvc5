; EXPECT: (:status unknown)

; This regression tests uses of s-expressions when the output-language is AST

(set-option :output-language ast)

(set-info :source (true false (- 15) 15 15.0 #b00001111 #x0f x |x 
"| "" """"))
(get-info :status)
