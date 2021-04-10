; EXPECT: (SEXPR (SEXPR check-sat (CONST_RATIONAL 2)) (SEXPR * (CONST_RATIONAL 1)))
; EXPECT: (:status unknown)

(set-option :output-language ast)
(set-option :command-verbosity (* 1))
(set-option :command-verbosity (check-sat 2))
(get-option :command-verbosity)

(set-info :source (0 1 True False ""))
(get-info :status)
