; COMMAND-LINE: --produce-models
; EXPECT: true
; EXPECT: false
; EXPECT: true
(get-option :produce-models)
(set-option :produce-models false)
(get-option :produce-models)
(reset)
(get-option :produce-models)
