;;;
;;; Copyright 2016, NICTA
;;;
;;; This software may be distributed and modified according to the terms of
;;; the GNU General Public License version 2. Note that NO WARRANTY is provided.
;;; See "LICENSE_GPLv2.txt" for details.
;;;
;;; @TAG(NICTA_GPL)
;;;

;; cogent.el  --- summary
;; A COGENT Emacs mode.
;;; Commentary:
;; This mode is currently using only the simplest highlighting techniques.
;; Hopefully this is sufficient for now.
;;; Code:
(require 'generic-x) ;; we need this

(define-generic-mode
  'cogent-mode
  '( ("{-" . "-}")
    )
  '("let" "in" "type" "include" "all" "world" "take" "put" "if" "then" "else" "not" "and")
  '( ("--.*\\s-*$" . 'font-lock-comment-face)
     ("![a-z][A-Za-z_'0-9]*" . 'font-lock-function-name-face)
     ("[A-Z][A-Za-z_'0-9]*" . 'font-lock-variable-name-face)
     ("[^A-Za-z'_]\\([0-9]+\\)" 1 'font-lock-constant-face)
     ("[^A-Za-z'_0-9]\\('[^']+'\\)" 1 'font-lock-string-face)
     (";" . 'font-lock-builtin-face)
     ("<" . 'font-lock-builtin-face)
     (">" . 'font-lock-builtin-face)
     ("!" . 'font-lock-builtin-face)
     ("=" . 'font-lock-builtin-face)
     ("-" . 'font-lock-builtin-face)
     ("|" . 'font-lock-builtin-face)
     ("^" . 'font-lock-builtin-face)
     ("\\." . 'font-lock-builtin-face)
     ("&" . 'font-lock-builtin-face)
     ("{" . 'font-lock-builtin-face)
     ("~" . 'font-lock-builtin-face)
     ("}" . 'font-lock-builtin-face)
     (":" . 'font-lock-builtin-face)
   )
  '("\\.cogent$" "\\.cogent$")
  nil
  "A mode for COGENT files"
  )

(provide 'cogent)
;;; cogent.el ends here
