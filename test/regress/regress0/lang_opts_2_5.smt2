; Check that the language set in the command line options has higher priority
; than the language specified in the input file.
;
; COMMAND-LINE: --lang=smt2.5
; EXPECT: "LANG_SMTLIB_V2_5"
(set-info :smt-lib-version 2.6)
(get-option :input-language)
