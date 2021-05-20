; EXPECT: "str"""
; EXPECT: "str""ing"
; EXPECT: "hi"
; EXPECT: "str""""ing"
; EXPECT: "str""i""ng"
; EXPECT: "str\ing"
; EXPECT: "str\\ing"
; EXPECT: "str\"
; EXPECT: "\u{65}"
(echo "str""")
(echo "str""ing")
(echo "hi")
(echo "str""""ing")
(echo "str""i""ng")
(echo "str\ing")
(echo "str\\ing")
(echo "str\")
(echo "\u{65}")
