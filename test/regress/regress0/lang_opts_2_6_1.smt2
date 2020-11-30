; Check that the language set in the command line options has higher priority
; than the language specified in the input file.
;
; COMMAND-LINE: --lang=smt2.6
; EXPECT: "LANG_SMTLIB_V2_6"
(set-info :smt-lib-version 2.6)
(get-option :input-language)
