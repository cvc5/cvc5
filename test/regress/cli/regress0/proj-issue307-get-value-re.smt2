; SCRUBBER: grep -v -E '\(error'
; EXPECT: sat
(reset)
(set-logic ALL)
(set-option :produce-models true)
(check-sat)
(get-value ((re.opt re.allchar)))
