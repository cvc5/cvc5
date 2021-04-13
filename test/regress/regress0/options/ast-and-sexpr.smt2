; EXPECT: (SEXPR (SEXPR check-sat (CONST_RATIONAL 2)) (SEXPR * (CONST_RATIONAL 1)))
; EXPECT: (:status unknown)

; This regression tests uses of s-expressions when the output-language is AST

(set-option :output-language ast)

; Set the verbosity of all commands to 1
(set-option :command-verbosity (* 1))
; Set the verbosity of (check-sat) command to 2
(set-option :command-verbosity (check-sat 2))
; Get the verbosity of all commands
(get-option :command-verbosity)
; There is no SMT option to get the verbosity of a specific command

(set-info :source (0 1 True False x ""))
(get-info :status)
