; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat
(set-logic UFDTSLIA)
(set-info :smt-lib-version 2.5)
(set-option :produce-models true)

(declare-datatypes () (
    (List_boolean (List_boolean$CNil_boolean) (List_boolean$Cstr_boolean (List_boolean$Cstr_boolean$head Bool) (List_boolean$Cstr_boolean$tail List_boolean)))
) )

(define-funs-rec
  (
    (f4208$lengthList_boolean((x List_boolean)) Int)
  )
  (
    (ite (is-List_boolean$CNil_boolean x) 0 (+ 1 (f4208$lengthList_boolean (List_boolean$Cstr_boolean$tail x))))
  )
)


(declare-const boolean Bool)
(check-sat)
