To match the CVC4 coding style, drop the following in your ~/.emacs,
replacing "/home/mdeters/cvc4.*" in the last line with a regexp
describing your usual cvc4 editing location(s):


; CVC4 mode
(defun cvc4-c++-editing-mode ()
  "C++ mode with adjusted defaults for use with editing CVC4 code."
  (interactive)
  (message "CVC4 variant of C++ mode activated.")
  (c++-mode)
  (setq c-basic-offset 2)
  (c-set-offset 'innamespace 0)
  (setq indent-tabs-mode nil))
(setq auto-mode-alist (cons '("/home/mdeters/cvc4.*/.*\\.\\(cc\\|cpp\\|h\\|hh\\|hpp\\)$" . cvc4-c++-editing-mode) auto-mode-alist))


-- Morgan Deters <mdeters@cs.nyu.edu>  Mon, 02 Nov 2009 18:19:22 -0500
