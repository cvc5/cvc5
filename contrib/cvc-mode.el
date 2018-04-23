;;;; /*!
;;;;  * \file cvc-mode.el
;;;;  * \brief Emacs mode for CVC programs in presentation language
;;;;  * 
;;;;  * Author: Sergey Berezin
;;;;  * 
;;;;  * Created: Mon Aug 11 12:29:32 2003
;;;;  *
;;;;  * <hr>
;;;;  *
;;;;  * License to use, copy, modify, sell and/or distribute this software
;;;;  * and its documentation for any purpose is hereby granted without
;;;;  * royalty, subject to the terms and conditions defined in the \ref
;;;;  * LICENSE file provided with this distribution.
;;;;  *
;;;;  * <hr>
;;;;  * 
;;;;  */

;;;; To use this library, place the following lines into your ~/.emacs file:
;;;;
;;;; ;;; CVC mode
;;;; (autoload 'cvc-mode "cvc-mode" "CVC specifications editing mode." t)
;;;; (setq auto-mode-alist 
;;;;       (append  (list '("\\.cvc$" . cvc-mode)) auto-mode-alist))
;;;;
;;;; Of course, the file cvc-mode.el must be in one of the directories in your
;;;; `load-path'. C-h v load-path to see the list, or `cons' your own path:
;;;; (setq load-path (cons "/the/full/path/to-your/dir" load-path))
;;;;
;;;; To turn the font-lock on by default, put in .emacs
;;;; (global-font-lock-mode t) ;; if you use gnu-emacs, or
;;;; (setq-default font-lock-auto-fontify t) ;; if you use xemacs.
;;;;
;;;; In GNU emacs faces `font-lock-preprocessor-face' and 
;;;; `font-lock-variable-name-face' may not be predefined.
;;;; In this case they are defined automatically when smv-mode.el
;;;; is loaded the first time. You can also define them yourself in .emacs:
;;;;
;;;; ;;; Make faces that are not in gnu-emacs font-lock by default
;;;; (defvar font-lock-preprocessor-face 'font-lock-preprocessor-face)
;;;; (defvar font-lock-variable-name-face 'font-lock-variable-name-face)
;;;; (make-face 'font-lock-preprocessor-face)
;;;; (make-face 'font-lock-variable-name-face)

(require 'font-lock)
(require 'compile)

(defvar cvc-font-lock-mode-on t
  "If not nil, turn the fontification on.")

;;;; Syntax definitions

(defvar cvc-mode-syntax-table nil  "Syntax table used while in CVC mode.")

(if cvc-mode-syntax-table ()
    (let ((st (syntax-table)))
      (unwind-protect
	   (progn
	     (setq cvc-mode-syntax-table (make-syntax-table))
	     (set-syntax-table cvc-mode-syntax-table)
	     (modify-syntax-entry ?_ "w")
	     (modify-syntax-entry ?- "w")
	     (modify-syntax-entry ?\? "w")
	     (modify-syntax-entry ?: "." )
	     (modify-syntax-entry ?% "<")
	     (modify-syntax-entry ?\f ">")
	     (modify-syntax-entry ?\n ">"))
	(set-syntax-table st))))

;;;; Fontification stuff

(defun cvc-keyword-match (keyword)
;  "Convert a string into a regexp matching any capitalization of that string."
  "Convert a string into a regexp matching that string as a separate word."
;  (let ((regexp "")
;	(index 0)
;	(len (length keyword)))
;    (while (< index len)
;      (let ((c (aref keyword index)))
;	(setq regexp
;	      (concat regexp (format "[%c%c]" (downcase c) (upcase c))))
;	(setq index (+ index 1))))
    (format "\\b%s\\b" keyword))
;)

(defvar cvc-font-lock-separator-face 'cvc-font-lock-separator-face)
(defvar font-lock-preprocessor-face 'font-lock-preprocessor-face)
(defvar font-lock-variable-name-face 'font-lock-variable-name-face)

(if (facep 'font-lock-preprocessor-face) ()
    (progn
      (make-face 'font-lock-preprocessor-face)
      (set-face-foreground 'font-lock-preprocessor-face "green4")))

(if (facep 'font-lock-variable-name-face) ()
    (progn
      (make-face 'font-lock-variable-name-face)
      (set-face-foreground 'font-lock-variable-name-face "deeppink")))

(if (facep 'cvc-font-lock-separator-face) ()
    (progn
      (make-face 'cvc-font-lock-separator-face)
      (set-face-foreground 'cvc-font-lock-separator-face "indianred")))

(defvar cvc-mode-hook nil
  "Functions to run when loading an CVC file.")

(defconst cvc-keywords
  '("ASSERT" "QUERY" "TRACE" "UNTRACE" "OPTION" "HELP" "TRANSFORM"
    "PRINT" "ECHO" "INCLUDE" "DUMP_ASSUMPTIONS" "DUMP_PROOF" "DUMP_SIG"
    "WHERE" "COUNTEREXAMPLE" "PUSH" "POP" "POP_SCOPE" "POPTO" "RESET"
    "CONTEXT"
    "TYPE" "DATATYPE" "SUBTYPE"
    "REAL" "INT" "BOOLEAN" "ARRAY" "OF"
    "TRUE" "FALSE" "FLOOR"
    "IF" "THEN" "ELSIF" "ELSE" "ENDIF" "LET" "IN" "END" "LAMBDA" "WITH"
    "FORALL" "EXISTS" 
    "AND" "OR" "XOR" "NOT" )
  "The list of CVC keywords.")

(defconst cvc-declaration-keywords
  '("ASSERT" "QUERY" "TRACE" "UNTRACE" "OPTION" "HELP" "TRANSFORM"
    "PRINT" "ECHO" "INCLUDE" "DUMP_ASSUMPTIONS" "DUMP_PROOF" "DUMP_SIG"
    "WHERE" "COUNTEREXAMPLE" "PUSH" "POP" "POP_SCOPE" "POPTO" "RESET"
    "CONTEXT")
  "The list of keywords that open a declaration. Used for indentation.")

(defconst cvc-declaration-keywords-regexp
  (mapconcat 'cvc-keyword-match cvc-declaration-keywords "\\|"))

(defconst cvc-openning-keywords
  '("case" "for" "next" "init")
  "The list of keywords that open a subexpression. Used for indentation.")

(defconst cvc-openning-keywords-regexp
  (mapconcat 'cvc-keyword-match cvc-openning-keywords "\\|"))

(defconst cvc-closing-keywords
  '("esac")
  "The list of keywords that close a subexpression. Used for indentation.")

(defconst cvc-closing-keywords-regexp
  (mapconcat 'cvc-keyword-match cvc-closing-keywords "\\|"))

(defconst cvc-infix-operators
  '("<->" "<-" "->" ":=" "<=w\\>" ">=w\\>" "<w\\>" ">w\\>" "=w\\>"
    "+w\\>" "-w\\>" "*w\\>" "<=" ">=" "!=" "=" "\\[" "\\]"
    "\\b-\\b" "+" "|" "&" "<" ">")
  "The list of regexps that match CVC infix operators. The distinction
is made primarily for indentation purposes.")

(defconst cvc-infix-operators-regexp
  (mapconcat 'identity cvc-infix-operators "\\|"))

(defconst cvc-other-operators
  '("!" "(#" "#)")
  "Non-infix CVC operators that are not listed in `cvc-infix-operators'.")

(defconst cvc-other-operators-regexp
  (mapconcat 'identity cvc-other-operators "\\|"))

(defconst cvc-operators (append cvc-infix-operators cvc-other-operators)
  "The list of regexps that match CVC operators. It is set to the
concatenation of `cvc-infix-operators' and `cvc-other-operators'.")

(defconst cvc-separator-regexp "[,.;():]"
  "A regexp that matches any separator in CVC mode.")

(defconst cvc-font-lock-keywords-1
  (purecopy
   (list
    (list (concat (cvc-keyword-match "MODULE") " *\\([-_?A-Za-z0-9]+\\)")
	  1 'font-lock-preprocessor-face)
    (list (concat "\\(" (cvc-keyword-match "init") "\\|"
		  (cvc-keyword-match "next")
		  "\\)(\\s-*\\([][_?.A-Za-z0-9-]+\\)\\s-*)\\s-*:=")
	  2 'font-lock-variable-name-face)
    ;;; For DEFINE and invar assignments
    (list "\\([][_?.A-Za-z0-9-]+\\)\\s-*:="
	  1 'font-lock-variable-name-face)
    (list "\\<\\([Aa]\\|[Ee]\\)\\[" 1 'font-lock-keyword-face)
    (list (concat "\\("
		  (mapconcat 'identity cvc-operators "\\|")
		  "\\)")
	  1 'font-lock-function-name-face 'prepend)
    (mapconcat 'cvc-keyword-match cvc-keywords "\\|")
;; Fix the `%' comments
    (list "\\(%.*$\\)" 1 'font-lock-comment-face t) ))
  "Additional expressions to highlight in CVC mode.")

(defconst cvc-font-lock-keywords-2
  (purecopy 
   (append cvc-font-lock-keywords-1
	   (list
	    (list "\\([{}]\\)" 1 'font-lock-type-face)
	    (list (concat "\\(" cvc-separator-regexp "\\)")
		  1 'cvc-font-lock-separator-face 'prepend))))
  "Additional expressions to highlight in CVC mode.")
  
(defconst cvc-font-lock-keywords
  (if font-lock-maximum-decoration
      cvc-font-lock-keywords-2
      cvc-font-lock-keywords-1))

(defun cvc-minimal-decoration ()
  (interactive)
  (setq font-lock-keywords cvc-font-lock-keywords-1))

(defun cvc-maximal-decoration ()
  (interactive)
  (setq font-lock-keywords cvc-font-lock-keywords-2))

;;;; Running CVC 

(defvar cvc-command "cvc3" 
  "The command name to run CVC. The default is usually \"cvc3\"")

(defvar cvc-sat-option nil
  "Search Engine choice in CVC.  Valid values are nil,
\"default\", \"simple\", and \"fast\", or any other values reported by
cvc3 -h.")

(defvar cvc-trace-flags nil
  "List of trace flags given on the command line as +trace options")

(defvar cvc-verbose-level nil
"The verbose mode of CVC. Valid values are nil and \"quiet\".  This
value is passed to the CVC process as +/-quiet opton.")

(defvar cvc-command-line-args nil
  "Miscellaneous CVC command line args.
Must be a single string or nil.")

(defvar cvc-compile-buffer nil
  "The buffer associated with inferior CVC process.
This variable is updated automatically each time CVC process takes off.")

(defvar cvc-options-changed nil)

(defvar cvc-current-buffer nil
  "The current CVC editing buffer.
This variable is buffer-local.")
(make-local-variable 'cvc-current-buffer)

(defun cvc-args (file &optional args)
  "Compiles the string of CVC command line args from various variables."
  (mapconcat 'identity
	     (append
	      (if cvc-sat-option (list "-sat" cvc-sat-option) nil)
	      (if (eq cvc-verbose-level "quiet") (list "+quiet") nil)
	      (mapcar '(lambda (str) (format "+trace \"%s\"" str)) cvc-trace-flags)
	      (if cvc-command-line-args (list cvc-command-line-args))
	      (if args (list args) nil)
	      (list "<" file))
	     " "))

(defun cvc-run ()
  "Runs CVC on the current buffer."
  (interactive)
  (let ((buffer (current-buffer)))
    (if (buffer-file-name)
	(progn
	  (if (buffer-modified-p) (cvc-save-buffer))
	  (setq cvc-compile-buffer 
		(compile-internal
		 (concat "time " cvc-command " " (cvc-args (buffer-file-name)))
				  "No more errors"
				  "CVC"))
	  (set-buffer cvc-compile-buffer) ;;; Doesn't work???
	  (end-of-buffer)
	  (set-buffer buffer)
	  )
    (error "Buffer does not seem to be associated with any file"))) )


(defun cvc-save-options ()
  "Saves current options in *.opt file."
  (interactive)
  (let* ((buffer (current-buffer))
	 (opt-file-name 
	  (let ((match (string-match "\\.cvc$"
				     (buffer-file-name))))
	    (if match
		(concat (substring (buffer-file-name)
				   0 match)
			".opt")
	      (concat (buffer-file-name) ".opt"))))
	 (opt-buffer-name 
	  (let ((match (string-match "\\.cvc$"
				     (buffer-name))))
	    (if match
		(concat (substring (buffer-name)
				   0 match)
			".opt")
	      (concat (buffer-name) ".opt"))))
	 (opt-buffer-exists (get-buffer opt-buffer-name))
	 (opt-buffer (get-buffer-create opt-buffer-name))
	 (save-options-from-buffer 
	  (and opt-buffer-exists 
	       (buffer-modified-p opt-buffer)
	       (y-or-n-p (format "buffer %s is modified. Save options from that buffer?" 
				 (buffer-name opt-buffer)))))
	 (options (format ";;;; This file is generated automatically.\n(setq cvc-sat-option %S)\n(setq cvc-verbose-level %S)\n(setq cvc-trace-flags '%S)\n(setq cvc-command-line-args %S)\n"
			  cvc-sat-option
			  cvc-verbose-level
			  cvc-trace-flags
			  cvc-command-line-args)))
    (set-buffer opt-buffer)
    (if save-options-from-buffer (cvc-save-and-load-options)
      (progn
	(erase-buffer)
	(insert options)
	(write-file opt-file-name)
	(kill-buffer opt-buffer)))
    (set-buffer buffer)
    (setq cvc-options-changed nil)
    (message "Options are saved.")))

(defun cvc-save-and-load-options ()
  "Saves the current buffer and updates CVC options in the associated
buffer.  This buffer is either the value of `cvc-current-buffer', or
it tries to make a few reasonable guesses. If no CVC buffer is found,
only saves the current buffer.

Normally is called from the *.opt file while editing options for CVC
specification." 
  (interactive)
  (let* ((buffer (current-buffer))
	 (buffer-file (buffer-file-name))
	 (cvc-buffer-name
	  (let* ((match (string-match "\\.[^.]*$" (buffer-name))))
	    (if match
		(concat (substring (buffer-name) 0 match) ".cvc")
	      (concat (buffer-name) ".cvc"))))
	 (cvc-buffer (get-buffer cvc-buffer-name))
	 (cvc-buffer
	  (cond (cvc-buffer cvc-buffer)
		((and (boundp 'cvc-current-buffer)
		      (buffer-live-p cvc-current-buffer))
		 cvc-current-buffer)
		(t nil))))
    (save-buffer)
    (if cvc-buffer
	(let ((cvc-window (get-buffer-window cvc-buffer))
	      (window (get-buffer-window buffer)))
	  (set-buffer cvc-buffer)
	  (load buffer-file)
	  (setq cvc-current-buffer cvc-buffer)
	  (if cvc-window 
	      (select-window cvc-window)
	    (switch-to-buffer cvc-buffer))
	  (if window
	      (delete-window window))
	  (setq cvc-options-changed nil)))) )

(defun cvc-save-and-return ()
  "Saves the current buffer and returns back to the associated CVC
buffer.  The CVC buffer is either the value of `cvc-current-buffer', or
it tries to make a few reasonable guesses. If no CVC buffer is found,
only saves the current buffer.

Normally is called from the *.ord buffer while editing variable ordering
for CVC specification. Bound to \\[cvc-save-and-return]"
  (interactive)
  (let* ((buffer (current-buffer))
	 (cvc-buffer-name
	  (let* ((match (string-match "\\.[^.]*$" (buffer-name))))
	    (if match
		(concat (substring (buffer-name) 0 match) ".cvc")
	      (concat (buffer-name) ".cvc"))))
	 (cvc-buffer (get-buffer cvc-buffer-name))
	 (cvc-buffer
	  (cond (cvc-buffer cvc-buffer)
		((and (boundp 'cvc-current-buffer)
		      (buffer-live-p cvc-current-buffer))
		 cvc-current-buffer)
		(t nil))))
    (save-buffer)
    (if cvc-buffer
	(let ((cvc-window (get-buffer-window cvc-buffer)))
	  (setq cvc-current-buffer cvc-buffer)
	  (if cvc-window 
	      (select-window cvc-window)
	    (switch-to-buffer cvc-buffer))
	  (if (get-buffer-window buffer) 
	      (delete-window (get-buffer-window buffer)))))) )

(defun cvc-edit-options ()
  "Loads current options in a new buffer and lets the user edit it.
Run \\[eval-buffer] when done."
  (interactive)
  (let* ((buffer (current-buffer))
	 (opt-buffer-name 
	  (let ((match (string-match "\\.cvc$"
				     (buffer-name))))
	    (if match
		(concat (substring (buffer-name)
				   0 match)
			".opt")
	      (concat (buffer-name) ".opt"))))
	 (opt-buffer (get-buffer-create opt-buffer-name))
	 	 (options (format ";;;; This file is generated automatically.\n(setq cvc-sat-option %S)\n(setq cvc-verbose-level %S)\n(setq cvc-trace-flags '%S)\n(setq cvc-command-line-args %S)\n"
			  cvc-sat-option
			  cvc-verbose-level
			  cvc-trace-flags
			  cvc-command-line-args)))
    (setq cvc-options-changed t)
    (switch-to-buffer-other-window opt-buffer)
    (set-visited-file-name opt-buffer-name)
    (erase-buffer)
    (insert options)
    (make-local-variable 'cvc-currect-buffer)
    (setq cvc-current-buffer buffer)
    (cvc-options-edit-mode)))

(defun cvc-interrupt ()
  "Kills current CVC process."
  (interactive)
  (quit-process (get-buffer-process cvc-compile-buffer) t))

(defun cvc-send-signal (sig)
  "Sends signal SIG to the CVC process. SIG must be an integer."
  (if (get-buffer-process cvc-compile-buffer)
      (if (file-exists-p ".cvc-pid")
	(save-excursion
	  (let ((buf (get-buffer-create ".cvc-pid")))
	    (set-buffer buf)
	    (erase-buffer)
	    (insert-file-contents ".cvc-pid")
	    (let ((pid (read buf)))
	      (if (integerp pid)
		  (signal-process pid sig)
		(error "The file .cvc-pid is screwed up: %s" pid)))
	    (kill-buffer buf)))
	(error "Your CVC version does not support signal handling"))
    (error "CVC is not running")))

(defun cvc-send-usr1 () 
  "Sends SIGUSR1 to the current CVC process. I have a version of CVC
that uses it to toggle dynamic variable ordering."
  (interactive)
  (cvc-send-signal 10))

(defun cvc-send-usr2 () 
  "Sends SIGUSR2 to the current CVC process. I have a version of CVC
that uses it to force garbage collection."
  (interactive)
  (cvc-send-signal 12))

(defun cvc-set-verbose-level (arg)
  "Sets CVC verbose level to use in command line option +/-quiet.
If empty line is given, use the default."
  (interactive (list (read-from-minibuffer "Set verbose level to: "
			       cvc-verbose-level)))
  (if (stringp arg)
      (progn
	(if (string= arg "") (setq cvc-verbose-level nil)
	  (setq cvc-verbose-level arg))
	(setq cvc-options-changed t))
    (error "Not a string. The value is not set.")))

(defun cvc-set-command (arg)
  "Sets the name of the CVC executable to run."
  (interactive (list (read-file-name "CVC binary: "
				     "" cvc-command nil cvc-command)))
  (if (stringp arg)
      (progn
	(if (string= arg "") nil
	  (setq cvc-command arg))
	(setq cvc-options-changed t))
    (error "Not a string. The value is not set.")))

(defun cvc-trace (arg)
  "Adds a CVC tracing flag to be given in the +trace command line option."
  (interactive (list (read-from-minibuffer "Add trace flag: "
			       cvc-verbose-level)))
  (if (stringp arg)
      (progn
	(if (string= arg "") (error "Empty flag is not allowed")
	  (setq cvc-trace-flags (add-to-list 'cvc-trace-flags arg)))
	(setq cvc-options-changed t)
	(message "%S" cvc-trace-flags))
    (error "Not a string. The value is not set.")))

(defun cvc-untrace (arg)
  "Removes a CVC tracing flag given in the +trace command line option."
  (interactive (list (completing-read "Remove trace flag: "
				      (mapcar '(lambda (x) (cons x t)) cvc-trace-flags)
				      nil t)))
  (if (stringp arg)
      (progn
	(if (string= arg "") nil ; don't do anything on empty input
	  (setq cvc-trace-flags (delete arg cvc-trace-flags)))
	(setq cvc-options-changed t)
	(message "%S" cvc-trace-flags))
    (error "Not a string. The value is not set.")))

(defun cvc-set-command-line-args (arg)
  "Sets CVC command line options. Don't set -sat and +quiet
options here, use corresponding special variables for that."
  (interactive (list (read-from-minibuffer "Other arguments: "
			       cvc-command-line-args)))
  (if (stringp arg)
      (progn 
	(if (string= arg "") (setq cvc-command-line-args nil)
	  (setq cvc-command-line-args arg))
	(setq cvc-options-changed t))
    (error "Not a string. The value is not set.")))

;;;; Saving file
(defun cvc-save-buffer ()
  "Saves CVC file together with options. Prompts the user whether to
override the *.opt file if the options have changed."
  (interactive)
  (let ((opt-file-name 
	 (let ((match (string-match "\\.cvc$"
				    (buffer-file-name))))
	   (if match
	       (concat (substring (buffer-file-name)
				  0 match)
		       ".opt")
	     (concat (buffer-file-name) ".opt")))))
    (cond ((and (file-exists-p opt-file-name)
		cvc-options-changed)
	     (if (y-or-n-p "Options have changed. Save them?")
		 (progn
		   (cvc-save-options)
		   (setq cvc-options-changed nil))))
	  (cvc-options-changed 
	     (cvc-save-options)
	     (setq cvc-options-changed nil))))
    (save-buffer))

;;;; Indentation

(defun cvc-previous-line ()
  "Moves the point to the fisrt non-comment non-blank string before
the current one and positions the cursor on the first non-blank character."
  (interactive)
  (forward-line -1)
  (beginning-of-line)
  (skip-chars-forward " \t")
  (while (and (not (bobp)) (looking-at "$\\|%"))
    (forward-line -1)
    (beginning-of-line)
    (skip-chars-forward " \t")))

(defun cvc-previous-indentation () 
  "Returns a pair (INDENT . TYPE). INDENT is the indentation of the
previous string, if there is one, and TYPE is 'openning, 'declaration
or 'plain, depending on whether previous string starts with an
openning, declarative keyword or neither. \"Previous string\" means
the last string before the current that is not an empty string or a
comment."
  (if (bobp) '(0 . 'plain)
    (save-excursion
      (cvc-previous-line)
      (let ((type (cond ((looking-at cvc-openning-keywords-regexp) 'openning)
			((looking-at cvc-declaration-keywords-regexp)
			 'declaration)
			(t 'plain)))
	    (indent (current-indentation)))
	(cons indent type)))))

(defun cvc-compute-indentation ()
  "Computes the indentation for the current string based on the
previous string. Current algorithm is too simple and needs
improvement."
  (save-excursion
   (beginning-of-line)
   (skip-chars-forward " \t")
   (cond ((looking-at cvc-declaration-keywords-regexp) 0)
	 (t (let* ((indent-data (cvc-previous-indentation))
		   (indent (car indent-data))
		   (type (cdr indent-data)))
	      (setq indent
		    (cond ((looking-at cvc-closing-keywords-regexp) 
			   (if (< indent 2) 0 (- indent 2)))
			  ((or (eq type 'openning) (eq type 'declaration))
			   (+ indent 2))
			  (t indent)))
	      indent)))))

(defun cvc-indent-line ()
  "Indent the current line relative to the previous meaningful line."
  (interactive)
  (let* ((initial (point))
	 (final (let ((case-fold-search nil))(cvc-compute-indentation)))
	 (offset0 (save-excursion
		    (beginning-of-line)
		    (skip-chars-forward " \t")
		    (- initial (point))))
	 (offset (if (< offset0 0) 0 offset0)))
    (indent-line-to final)
    (goto-char (+ (point) offset))))

;;;; Now define the keymap

(defconst cvc-mode-map nil  "CVC keymap")

(if cvc-mode-map ()
  (progn
    (setq cvc-mode-map (make-sparse-keymap))
    (define-key cvc-mode-map [delete] 'backward-delete-char-untabify)
    (define-key cvc-mode-map [backspace] 'backward-delete-char-untabify)
    (define-key cvc-mode-map "\C-x\C-s"  'cvc-save-buffer)
    (define-key cvc-mode-map "\C-c\C-e"  'cvc-edit-options)
    (define-key cvc-mode-map "\C-c\C-f"  'cvc-run)
    (define-key cvc-mode-map "\C-c\C-t"  'cvc-trace)
    (define-key cvc-mode-map "\C-c\C-u"  'cvc-untrace)
    (define-key cvc-mode-map "\C-c\C-r"  'cvc-set-command)
    (define-key cvc-mode-map "\C-c\C-c"  'cvc-interrupt)
    ;; (define-key cvc-mode-map "\C-c\C-r"  'cvc-send-usr1)
    ;; (define-key cvc-mode-map "\C-c\C-s"  'cvc-send-usr2)
    (define-key cvc-mode-map "\C-c;"  'comment-region)
    (define-key cvc-mode-map "\t"  'cvc-indent-line)))

(defun cvc-make-local-vars ()
  "Create buffer-local variables for CVC modes"
  (make-local-variable 'cvc-command)
  (make-local-variable 'cvc-sat-option)
  (make-local-variable 'cvc-verbose-level)
  (make-local-variable 'cvc-trace-flags)
  (make-local-variable 'cvc-command-line-args)
  (make-local-variable 'cvc-options-changed)
  (make-local-variable 'cvc-options-changed))

(defun cvc-mode ()
  "Major mode for CVC specification files. 

\\{cvc-mode-map}

\\[cvc-run] runs CVC on buffer, \\[cvc-interrupt] interrupts already
running CVC process.

\\[cvc-send-usr1] and \\[cvc-send-usr2] are used to send UNIX signals
to CVC process to toggle dynamic variable ordering and force garbage
collection respectively. Available only for a new (experimental) CVC
version.

Running CVC (\\[cvc-run]) creates a separate buffer where inferior CVC
process will leave its output. Currently, each run of CVC clears the
compilation buffer. If you need to save multiple runs, save them one
at a time.

Please report bugs to barrett@cs.stanford.edu."
  (interactive)
  (use-local-map cvc-mode-map)
;;; Disable asking for the compile command
  (make-local-variable 'compilation-read-command)
  (setq compilation-read-command nil)
;;; Make all the variables with CVC options local to the current buffer
  (cvc-make-local-vars)
  (setq cvc-options-changed nil)
;;; Change the regexp search to be case sensitive
;;  (setq case-fold-search nil)
;;; Set syntax table
  (set-syntax-table cvc-mode-syntax-table)
  (make-local-variable 'comment-start)
;; fix up comment handling
  (setq comment-start "%")
  (make-local-variable 'comment-end)
  (setq comment-end "")
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "%+\\s-*")
  (setq require-final-newline t)
;;; Define the major mode
  (setq major-mode 'cvc-mode)
  (setq mode-name "CVC")
;;; Load command line options for CVC process
  (let ((opt-file-name 
	 (let ((match (string-match "\\.cvc$"
				    (buffer-file-name))))
	   (if match
	       (concat (substring (buffer-file-name)
				  0 match)
		       ".opt")
	     (concat (buffer-file-name) ".opt")))))
    (if (file-exists-p opt-file-name)
	(load opt-file-name)))
;;; Do fontification, if necessary
  (setq font-lock-keywords 
	(if font-lock-maximum-decoration
	    cvc-font-lock-keywords-2
	  cvc-font-lock-keywords-1))
  (if running-xemacs
      (put 'cvc-mode 'font-lock-defaults
	   '(cvc-font-lock-keywords nil nil nil nil))
    (setq font-lock-defaults '(cvc-font-lock-keywords nil nil nil nil)))
    (if (and cvc-font-lock-mode-on (or running-xemacs font-lock-global-modes)
	     window-system)
	(font-lock-mode 1))
  (setq mode-line-process nil) ; put 'cvc-status when hooked up to inferior CVC
  (run-hooks 'cvc-mode-hook))

(defun cvc-options-edit-mode ()
  "Major mode for editing CVC options. Actually, this is Emacs Lisp
mode with a few changes. In particular, \\[cvc-save-and-load-options] will save the file, 
find the associated CVC file and updates its options accordingly.  See
`\\[describe-bindings]' for key bindings.  "
  (interactive)
  (emacs-lisp-mode)
;;; Make all the variables with CVC options local to the current buffer
;;; to avoid accidental override of the global values
  (cvc-make-local-vars)
  (setq major-mode 'cvc-options-edit-mode)
  (setq mode-name "CVC Options")
  (if (and cvc-font-lock-mode-on (or running-xemacs font-lock-global-modes)
	   window-system)
      (font-lock-mode t))
  (use-local-map (copy-keymap (current-local-map)))
  (local-set-key "\C-c\C-c" 'cvc-save-and-load-options))

(provide 'cvc-mode)
