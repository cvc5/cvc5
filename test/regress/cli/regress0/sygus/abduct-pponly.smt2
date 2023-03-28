; EXPECT: fail
(set-logic ALL)
(set-option :preprocess-only true)
(set-option :preregister-mode lazy)
(set-option :produce-abducts true)
(declare-fun x (Int) Bool)
(get-abduct A (x 0))
