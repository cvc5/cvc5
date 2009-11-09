;;;; Add to your ~/.emacs the following lines:
;;;;
;;;;   (load-path "/full/path/to/this/file")
;;;;   (require 'cvc-devel)
;;;;   
;;;; If you want to modify the key binding for inserting the comment,
;;;; add also something like this:
;;;;
;;;;   (setq cvc-devel-comment-key "\M-/")
;;;;

(defvar cvc-devel-comment-key "\C-c\C-h"
  "The hot key binding to insert an appropriate comment in C++ header
in CVC code")

(require 'cc-mode)
(add-to-list 'c++-mode-hook
	     '(lambda ()
		(local-set-key cvc-devel-comment-key
			       'insert-comment-template)))

(defun insert-comment-template ()
  "Insert a comment template into C++ file in the CVC style.  The
comment is different depending on where it is inserted.  For example,
inserting it in the empty file will produce a file comment, a class
comment will be inserted before a class definition, and so on."
  (interactive)
  ; Check for macro
  (cond
   ((catch 'not-macro
      (progn
	(set-mark (point))
	(cond ((not (search-forward "#define" nil t))
	       (throw 'not-macro t)))
	(beginning-of-line)
	(cond ((not (= (mark) (point)))
	       (progn
		 (goto-char (mark))
		 (throw 'not-macro t))))
	; It's a macro: insert the comment template
	(forward-char 7)
	(re-search-forward "[^ ]")
	(backward-char)
	(set-mark (point))
	(re-search-forward " \\|(\\|^")
	(backward-char)
	(copy-region-as-kill (mark) (point))
	(beginning-of-line)
	(insert-string
"/*****************************************************************************/
/*!
 *\\def ")
	(yank)
	(insert-string "
 *
 * Author: ")
        (insert-string (user-full-name))
        (insert-string "
 *
 * Created: ")
	(insert-string (current-time-string))
	(insert-string "
 *
 * 
 */
/*****************************************************************************/
")
	(forward-line -3)
	(search-forward "* ")
	()
      )
    )
    (cond
     ((catch 'not-function
	(progn
	  (set-mark (point))
	  (cond ((not (search-forward "(" nil t))
		 (throw 'not-function t)))
	  (beginning-of-line)
	  (cond ((not (= (mark) (point)))
		 (progn
		   (goto-char (mark))
		   (throw 'not-function t))))
       	  ; It's a function: insert the comment template
	  (search-forward "(")
	  (re-search-backward "[^ ] *(")
	  (forward-char)
	  (set-mark (point))
	  (re-search-backward " \\|^.")
	  (re-search-forward "[^ ]")
	  (backward-char)
	  (copy-region-as-kill (mark) (point))
	  (beginning-of-line)
	  (insert-string
"/*****************************************************************************/
/*!
 * Function: ")
	  (yank)
	  (insert-string "
 *
 * Author: ")
          (insert-string (user-full-name))
          (insert-string "
 *
 * Created: ")
	  (insert-string (current-time-string))
	  (insert-string "
 *
 * 
 */
/*****************************************************************************/
")
	  (forward-line -3)
	  (search-forward "* ")
	  ()
	  )
	)
      (cond
       ((catch 'not-class
	  (progn
	    (set-mark (point))
	    (cond ((not (search-forward "class" nil t))
		   (throw 'not-class t)))
	    (beginning-of-line)
	    (cond ((not (= (mark) (point)))
		 (progn
		   (goto-char (mark))
		   (throw 'not-class t))))
       	    ; It's a class definition: insert the comment template
	    (forward-char 5)
	    (re-search-forward "[^ ]")
	    (backward-char)
	    (set-mark (point))
	    (re-search-forward "^\\| \\|{")
	    (backward-char)
	    (copy-region-as-kill (mark) (point))
	    (beginning-of-line)
	    (insert-string
"/*****************************************************************************/
/*!
 *\\class ")
	  (yank)
	  (insert-string "
 *\\brief ")
          (yank)
          (insert-string "
 *
 * Author: ")
          (insert-string (user-full-name))
          (insert-string "
 *
 * Created: ")
	  (insert-string (current-time-string))
	  (insert-string "
 *
 * 
 */
/*****************************************************************************/
")
	    (forward-line -4)
	    (search-forward "* ")
	    ()
	    )
	  )
	(cond
	 ((catch 'not-bof
	    (progn
	      (set-mark (point))
	      (beginning-of-buffer)
	      (cond ((not (= (mark) (point)))
		     (progn
		       (goto-char (mark))
		       (throw 'not-bof t))))
              ; At beginning of file: insert beginning of file comment
	      (insert-string
"/*****************************************************************************/
/*!
 *\\file ")
              (insert-string (file-name-nondirectory (buffer-file-name)))
	      (insert-string "
 *\\brief 
 *
 * Author: ")
          (insert-string (user-full-name))
          (insert-string "
 *
 * Created: ")
	      (insert-string (current-time-string))
	      (insert-string "
 */
/*****************************************************************************/
")
	      (forward-line -7)
	      (search-forward "brief ")
	      ()
	    )
	  )
          ; Insert default comment template
	  (insert-string
"/*****************************************************************************/
/*
 * 
 */
/*****************************************************************************/
")
	  (forward-line -3)
	  (search-forward "* ")
         )
	)
       )
      )
     )
    )
   )
  )
)

(provide 'cvc-devel)
