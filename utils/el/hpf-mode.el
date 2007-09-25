;;;###autoload

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) Heng Jiang, Uni Bremen 2007
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Version number
(defconst hpf-mode-version "0.1"
  "Version of HPF-Mode")

(defgroup hpf nil
  "Major mode for editing (heterogeneous) HPF specifications."
  :group 'languages
  :prefix "hpf-")

(defvar hpf-mode-hook nil)
(defvar hpf-mode-map (let ((keymap (make-keymap)))
			(define-key keymap "\C-c\C-c" 'comment-region)
			keymap) 
  "Keymap for HPF major mode")

;; Are we running FSF Emacs or XEmacs?
(defvar hpf-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

;; ====================== S Y N T A X   T A B L E ==================
;; Syntax table for HPF major mode
(defvar hpf-mode-syntax-table nil
  "Syntax table for HPF mode.")

(if hpf-mode-syntax-table
    ()
  (let ((table (make-syntax-table)))
    ;; Indicate that underscore may be part of a word
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?\t " " table)
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\' "\'" table)

    (mapcar (lambda (x)
	      (modify-syntax-entry x "_" table))
	    ;; Some of these are actually OK by default.
	    "!#$&*+.,/\\\\:<=>?@^|~")
    ;; commenting-out plus including other kinds of comment
    (setq hpf-mode-syntax-table table))
  )

;; Various mode variables.
(defun hpf-vars ()
  (kill-all-local-variables)
  (make-local-variable 'comment-start)
  (setq comment-start "#")
  (make-local-variable 'comment-padding)
  (setq comment-padding 0)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "#")      ;; %[%{[]() *")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-indent-function)
)

;; ============= K E Y W O R D   H I G H L I G H T I N G ============
(defface hpf-black-komma-face
  `((t (:foreground "black")))
  ""
  :group 'basic-faces)

(defface hpf-blue-komma-face
  `((t (:foreground "blue")))
  ""
  :group 'basic-faces)

(defvar hpf-black-komma-face 'hpf-black-komma-face
  "Face name to use for black komma.")

(defvar  hpf-annotation-face 'hpf-annotation-face
   "HPF mode face for Annotations")
(setq hpf-annotation-face 'font-lock-constant-face)

(defvar hpf-name-face 'hpf-name-face)
(setq hpf-name-face 'font-lock-variable-name-face)

(defvar hpf-keyword-face 'hpf-keyword-face)
(setq hpf-keyword-face 'font-lock-keyword-face)

(defvar hpf-library-name-face 'hpf-library-name-face)
(setq hpf-library-name-face 'font-lock-type-face)

(defvar hpf-builtin-face 'hpf-builtin-face)
(setq hpf-builtin-face 'font-lock-builtin-face)

(defvar hpf-comment-face 'hpf-comment-face)
(setq hpf-comment-face 'font-lock-comment-face)

(defvar hpf-other-name-face 'hpf-other-name-face)
(if (featurep 'xemacs)
    (setq hpf-other-name-face 'hpf-blue-komma-face)
  (setq hpf-other-name-face 'font-lock-function-name-face)
)

(defvar hpf-string-char-face 'hpf-string-char-face)
(setq hpf-string-char-face 'font-lock-string-face)

;; Syntax highlighting of HPF
;; "Warning: Do not design an element of font-lock-keywords to match 
;;  text which spans lines; this does not work reliably. While 
;;  font-lock-fontify-buffer handles multi-line patterns correctly, 
;;  updating when you edit the buffer does not, since it considers 
;;  text one line at a time." (from the GNU Emacs Lisp Reference Manual)

;; order of all the following highlighting rules is significant,
;; ony change if really needed

 ;; Comment
(defconst hpf-font-lock-specialcomment
	 (list    
	  '("#.*$" (0 (symbol-value 'hpf-comment-face) keep t)))
	 "Special Comment")

(defconst hpf-font-lock-keywords
  (append hpf-font-lock-specialcomment
   (list
   ;; commands
   '("\\(\\<\\|\\s-+\\)\\(use\\|dg\\|dg-all\\|show-dg-goals\\|show-theory-goals\\|show-theory\\|node-info\\|show-taxonomy\\|show-concepts\\|translate\\|prover\\|proof-script\\|cons-check\\|prove\\|prove-all\\)[ \t\n]"  
     (2 (symbol-value 'hpf-keyword-face) keep t))
   ;; axiom-selection
   '("\\(\\<\\|\\s-+\\)\\(with\\|excluding\\)[ \t\n]"  
     (2 (symbol-value 'hpf-keyword-face) keep t))
   ;; dg-commands
   '("\\(\\<\\|\\s-+\\)\\(auto\\|glob-subsume\\|glob-decomp\\|loc-infer\\|loc-decomp\\|hide-thm\\|thm-hide\\|basic\\)[ \t\n]"  
     (2 (symbol-value 'hpf-keyword-face) keep t))
   ))	
   "Reserved keywords highlighting")

;; String and Char
(defconst hpf-font-lock-string
  (append hpf-font-lock-keywords
	  (list '("\\(\\(\"\\|^>[ \t]*\\\\\\)\\([^\"\\\\\n]\\|\\\\.\\)*\\(\"\\|\\\\[ \t]*$\\)\\|'\\([^'\\\\\n]\\|\\\\.[^'\n]*\\)'\\)" 
		  (0 (symbol-value 'hpf-string-char-face) keep t))
	  ))
  "Syntax highlighting of String and Char") 

;; Define default highlighting level
;; (defvar hpf-font-lock-syntax-highligthing hpf-font-lock-keywords
(defvar hpf-font-lock-syntax-highligthing (symbol-value 'hpf-font-lock-string)
  "Default syntax highlighting level in HPF mode")

;; ================= C A S L   M A J O R   M O D E ===============
;; hpf major mode setup
;; Definition of HPF major mode
(defun hpf-mode ()
  "Major mode for editing HPF models"
  (interactive)
  (hpf-vars)
  (setq major-mode 'hpf-mode)
  (setq mode-name "HPF")
  ;; Load keymap
  (use-local-map hpf-mode-map)
  ;; Load syntax table
  (set-syntax-table hpf-mode-syntax-table)
  ;; (hpf-create-syntax-table)
  ;; Highlight HPF keywords
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults
	'(hpf-font-lock-syntax-highligthing))
  (make-local-variable 'font-lock-keywords-only)
  (setq font-lock-keywords-only nil)
  ;; Support for compile.el
  ;; We just substitute our own functions to go to the error.
  (run-hooks 'hpf-mode-hook)
  )
(provide 'hpf-mode)

;; HPF-mode ends here
