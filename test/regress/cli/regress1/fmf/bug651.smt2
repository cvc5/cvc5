; COMMAND-LINE: --fmf-fun --fmf-bound
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic UFDTSLIA)
(set-option :produce-models true)

(declare-datatypes ((Conditional_Int 0) (Conditional_T_titleType 0) (Conditional_boolean 0) (Conditional_string 0) (Double 0) (List_T_titleType 0) (List_boolean 0) (List_string 0) (T_titleType 0)) (
    ((Conditional_Int$CAbsent_Int) (Conditional_Int$CPresent_Int (Conditional_Int$CPresent_Int$value Int)))
    ((Conditional_T_titleType$CAbsent_T_titleType) (Conditional_T_titleType$CPresent_T_titleType (Conditional_T_titleType$CPresent_T_titleType$value T_titleType)))
    ((Conditional_boolean$CAbsent_boolean) (Conditional_boolean$CPresent_boolean (Conditional_boolean$CPresent_boolean$value Bool)))
    ((Conditional_string$CAbsent_string) (Conditional_string$CPresent_string (Conditional_string$CPresent_string$value String)))
    ((Double$CINF) (Double$CNINF) (Double$CNaN) (Double$CValue (Double$CValue$value Int)))
    ((List_T_titleType$CNil_T_titleType) (List_T_titleType$Cstr_T_titleType (List_T_titleType$Cstr_T_titleType$head T_titleType) (List_T_titleType$Cstr_T_titleType$tail List_T_titleType)))
    ((List_boolean$CNil_boolean) (List_boolean$Cstr_boolean (List_boolean$Cstr_boolean$head Bool) (List_boolean$Cstr_boolean$tail List_boolean)))
    ((List_string$CNil_string) (List_string$Cstr_string (List_string$Cstr_string$head String) (List_string$Cstr_string$tail List_string)))
    ((T_titleType$C_T_titleType (T_titleType$C_T_titleType$base String)))
))

(define-fun f1361$isValid_string((x String)) Bool true)
(define-fun f5131$isValid_T_titleType((x T_titleType)) Bool (and (f1361$isValid_string (T_titleType$C_T_titleType$base x)) (<= (str.len (T_titleType$C_T_titleType$base x)) 80)))
(define-funs-rec
  (
    (f5242$isValidElementsList_T_titleType((x List_T_titleType)) Bool)
  )
  (
    (=> ((_ is List_T_titleType$Cstr_T_titleType) x) (and (f5131$isValid_T_titleType (List_T_titleType$Cstr_T_titleType$head x)) (f5242$isValidElementsList_T_titleType (List_T_titleType$Cstr_T_titleType$tail x))))
  )
)
(define-fun f1348$isValid_boolean((x Bool)) Bool true)
(define-funs-rec
  (
    (f4169$isValidElementsList_boolean((x List_boolean)) Bool)
  )
  (
    (=> ((_ is List_boolean$Cstr_boolean) x) (and (f1348$isValid_boolean (List_boolean$Cstr_boolean$head x)) (f4169$isValidElementsList_boolean (List_boolean$Cstr_boolean$tail x))))
  )
)


(declare-const title T_titleType)
(check-sat)
