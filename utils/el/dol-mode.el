;;;###autoload
(autoload 'turn-on-dol-indent "dol-indent" "Turn on DOL indentation." t)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) University of Magdeburg, 2007-2016
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Version number
(defconst dol-mode-version "0.4"
  "Version of DOL-Mode")

(defgroup dol nil
  "Major mode for editing (heterogeneous) DOL specifications."
  :group 'languages
  :prefix "dol-")


(defvar dol-mode-hook nil)
(defvar dol-mode-map (let ((keymap (make-keymap)))
			(define-key keymap "\C-c\C-r" 'dol-run-hets-r)
			(if (featurep 'xemacs)
			    (define-key keymap "\C-c\C-u" 'dol-run-hets-g)
			  (define-key keymap "\C-c\C-c" 'dol-run-hets-g))
			(define-key keymap "\C-c\C-n" 'dol-compile-goto-next-error)
			keymap)
  "Keymap for DOL major mode")

;; Are we running FSF Emacs or XEmacs?
(defvar dol-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

;; ====================== S Y N T A X   T A B L E ==================
;; Syntax table for DOL major mode
(defvar dol-mode-syntax-table nil
  "Syntax table for DOL mode.")

(if dol-mode-syntax-table
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
    ;; Comments
    (cond ((featurep 'xemacs)
	   (modify-syntax-entry ?( "()" table)
	   (modify-syntax-entry ?) ")(" table)
	   (modify-syntax-entry ?{ "(}2" table)
	   (modify-syntax-entry ?} "){3" table)
	   (modify-syntax-entry ?[  "(]2" table)
	   (modify-syntax-entry ?]  ")[3" table)
	   (modify-syntax-entry ?%  "_ 14" table))
	  (t

	   (modify-syntax-entry ?\( "()" table)
	   (modify-syntax-entry ?\) ")(" table)
	   (modify-syntax-entry ?{ "(} 2n" table)
	   (modify-syntax-entry ?} "){ 3n" table)
	   (modify-syntax-entry ?% ". 14nb" table)
	   (modify-syntax-entry ?\[ "(] 2n" table)
	   (modify-syntax-entry ?\] ")[ 3n" table))
	   )
    (setq dol-mode-syntax-table table))
  )

;; Various mode variables.
(defun dol-vars ()
  (kill-all-local-variables)
  (make-local-variable 'comment-start)
  (setq comment-start "%[")
  (make-local-variable 'comment-padding)
  (setq comment-padding 0)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "%[{[]")      ;; %[%{[]() *")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'dol-comment-indent)
  (make-local-variable 'comment-end)
  (setq comment-end "]%")
  (set (make-local-variable 'comment-end-skip) "[\]}]%")
)

;; Find the indentation level for a comment.
(defun dol-comment-indent ()
  (skip-chars-backward " \t")
  ;; if the line is blank, put the comment at the beginning,
  ;; else at comment-column
  (if (bolp) 0 (max (1+ (current-column)) comment-column)))

;; ============= K E Y W O R D   H I G H L I G H T I N G ============
(defface dol-black-komma-face
  `((t (:foreground "black")))
  ""
  :group 'basic-faces)

(defface dol-blue-komma-face
  `((t (:foreground "blue")))
  ""
  :group 'basic-faces)

(defvar dol-black-komma-face 'dol-black-komma-face
  "Face name to use for black komma.")

(defvar  dol-annotation-face 'dol-annotation-face
   "DOL mode face for Annotations")
(setq dol-annotation-face 'font-lock-constant-face)

(defvar dol-name-face 'dol-name-face)
(setq dol-name-face 'font-lock-variable-name-face)

(defvar dol-keyword-face 'dol-keyword-face)
(setq dol-keyword-face 'font-lock-keyword-face)

(defvar dol-library-name-face 'dol-library-name-face)
(setq dol-library-name-face 'font-lock-type-face)

(defvar dol-builtin-face 'dol-builtin-face)
(setq dol-builtin-face 'font-lock-builtin-face)

(defvar dol-comment-face 'dol-comment-face)
(setq dol-comment-face 'font-lock-comment-face)

(defvar dol-other-name-face 'dol-other-name-face)
(if (featurep 'xemacs)
    (setq dol-other-name-face 'dol-blue-komma-face)
  (setq dol-other-name-face 'font-lock-function-name-face)
)

(defvar dol-string-char-face 'dol-string-char-face)
(setq dol-string-char-face 'font-lock-string-face)

;; Syntax highlighting of DOL
;; "Warning: Do not design an element of font-lock-keywords to match
;;  text which spans lines; this does not work reliably. While
;;  font-lock-fontify-buffer handles multi-line patterns correctly,
;;  updating when you edit the buffer does not, since it considers
;;  text one line at a time." (from the GNU Emacs Lisp Reference Manual)

;; order of all the following highlighting rules is significant,
;; ony change if really needed

 ;; Comment
(defconst dol-font-lock-specialcomment
	 (list
	  '("%%.*$" (0 (symbol-value 'dol-comment-face) keep t)))
	 "Special Comment")

;; Alternativ for Annotation
(defconst dol-font-lock-annotations
  (append dol-font-lock-specialcomment
	  (list
	   ;; always highlight closing )%
	   '("\\(\)%\\)[^%]"
	     (1 (symbol-value 'dol-annotation-face) keep t))
	   ;; %words \n
	   '("%\\w+\\b[^\n]*$"
	     (0 (symbol-value 'dol-annotation-face) keep t))
	   ;; %(.....)%
	   '("[^%]\\(%\([^)]*?\)%\\)[^%]"
	     (1 (symbol-value 'dol-annotation-face) keep t))
	   ;; %word( ... )%
	   '("\\(%\\sw+\([^)]*?\)%\\)[^%]"
	     (1 (symbol-value 'dol-annotation-face) keep t))
	   ))
  "Annotation")

(defconst dol-font-lock-keywords
  (append dol-font-lock-annotations
   (list
   ;; reserved keyword
   '("\\(\\<\\|\\s-+\\)\\(/\\\\\\|\\\\/\\|=>\\|<=>\\|and\\|arch\\|assoc\\|behaviourally\\|closed\\|comm\\|else\\|end\\|exists\\|fit\\|flexible\\|forall\\|free\\|generated\\|given\\|idem\\|if\\|local\\|modality\\|not\\|orElse\\|unit\\|when\\|alignment\\|along\\|assuming\\|and\\|closed-world\\|cofree\\|combine\\|cons-ext\\|end\\|entails\\|entailment\\|equivalence\\|excluding\\|extract\\|free\\|hide\\|import\\|in\\|for\\|forget\\|interpretation\\|keep\\|language\\|library\\|logic\\|maximize\\|model\\|minimize\\|network\\|ni\\|of\\|oms\\|onto\\|ontology\\|pattern\\|refined\\|refinement\\|reject\\|relation\\|remove\\|result\\|reveal\\|select\\|separators\\|serialization\\|spec\\|specification\\|substitution\\|syntax\\|then\\|to\\|translation\\|using\\|vars\\|via\\|view\\|where\\|with\\|cons\\|ccons\\|complete\\|consistent\\|def\\|implied\\|inconsistent\\|mcons\\|mono\\|notccons\\|notmcons\\|prefix\\|wdef\\|within\\|\\(\\(op\\|pred\\|var\\|type\\|sort\\)s?\\)\\)[,;]?[ \t\n]"
     (2 (symbol-value 'dol-keyword-face) keep t))
   '("[,;.]" (0 (symbol-value 'dol-black-komma-face) t t))
   ;; after forall don't highlight
   '("\\bforall\\b\\(.*\\)"
     (1 (symbol-value 'dol-black-komma-face) keep t))
   ;; Keywords of loading Library
   '("\\(\\<\\|\\s-+\\)\\(logic\\|from\\|get\\|library\\|version\\)[ :\t\n]+"
     (2 (symbol-value 'dol-builtin-face) keep t))
   ;; Library and Logic name
   '("\\b\\(library\\|logic\\)\\s-+\\(\\(\\w\\|/\\)+\\)\\(\\s-*->\\s-*\\(\\(\\w\\|/\\)+\\)\\)?[ \t\n]"
     (2 (symbol-value 'dol-library-name-face) keep t)
     (5 (symbol-value 'dol-library-name-face) keep t))
   ;; name of from, get and given
   '("\\b\\(get\\|given\\)[ \t\n]+\\(\\(\\sw+\\s-*\\(,[ \t\n]*\\|$\\)\\)+\\)\\(=\\|:\\|$\\)"
     (2 (symbol-value 'dol-name-face) t t))
   '("\\bfrom[ \t]+\\(.+\\)\\(get\\|$\\)"
     (1 (symbol-value 'dol-library-name-face) keep t))
   ;; the name of specification and view
   '("\\(\\<\\|\\[\\)\\(spec\\|view\\)\\s-+\\(\\w+\\)[ \t]*\\(\\[\\s-*\\([A-Z]\\w*\\).*\\s-*\\]\\)?\\s-*.*\\([]=:]\\|::=\\)"
     (3 (symbol-value 'dol-name-face) keep t)
     (5 (symbol-value 'dol-name-face) keep t))
   ;; then, and + name
   '("\\b\\(and\\|then\\)[ \t\n]*\\([A-Z]\\w*\\)\\s-*\\(\\[\\([A-Z]\\sw*\\).*\\]\\)?"
     (2 (symbol-value 'dol-name-face) keep t)
     (4 (symbol-value 'dol-name-face) keep t))
   ;; names before and after to
   '("[ \t\n]*\\(\\sw+\\)[ \t\n]+to[ \t\n]+\\(\\(\\sw+\\)\\s-*\\(\\[\\([A-Z]\\sw*\\).*\\]\\)?[, \t]*\\)?"
     (1 (symbol-value 'dol-name-face) keep t)
     (3 (symbol-value 'dol-name-face) keep t)
     (5 (symbol-value 'dol-name-face) keep t))
   ;; instance name of specification
   '("\\<spec.+=\\s-*\\(%\\sw+\\s-*\\)?[ \t\n]*\\([A-Z]\\w*\\)\\s-*\\(\\[\\s-*\\([A-Z]\\w*\\).*\\s-*\\]\\)?"
     (2 (symbol-value 'dol-name-face) keep t)
     (4 (symbol-value 'dol-name-face) keep t))
   ;; Basic signature: sort X, Y, Z
   '("\\(\\<\\|\\s-+\\)sorts?[ \t\n]+\\(\\(\\sw+\\s-*\\(\\[\\s-*\\(\\sw\\|,\\)+\\s-*\\]\\s-*\\)?\\(,\\(\\s-\\)*\\|$\\|<\\|;\\|=\\)\\(=\\|<\\|;\\|,\\)*[ \t\n]*\\)+\\)"
     (2 (symbol-value 'dol-other-name-face) keep t))
   ;; Basic signature: op ,pred and var name
   '("\\(\\(^[^.{%]\\)\\s-*\\|\\bops?\\b\\|\\bpreds?\\b\\|\\bvars?\\b\\)\\([^:{()\n]*\\)\\(\(.*\)\\)?:\\??[^?.:=%].*;?[ \t]*$"
     (2 (symbol-value 'dol-other-name-face) keep t)
     (3 (symbol-value 'dol-other-name-face) keep t))
   ;; highlight a line with , an end
   '("^\\(\\(\\(__\\s-*[^_\n]+\\s-*__\\|[^.,:>\n]+\\)\\s-*,\\s-*\\)+\\)$"
     (0 (symbol-value 'dol-other-name-face) keep t))
   ;; names before and after '|->'
   '("[ \t\n]*\\(__[^|_]+__\\|[^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[ \t\n]*|->[ \t\n]*\\(__[^|_]+__\\|[^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[, \t]*"
     (1 (symbol-value 'dol-other-name-face) keep t)
     (3 (symbol-value 'dol-other-name-face) keep t)
     (4 (symbol-value 'dol-other-name-face) keep t)
     (6 (symbol-value 'dol-other-name-face) keep t))
   ;; type name
   '("\\(\\btype\\|\\bfree type\\)?\\s-+\\(\\sw+\\)\\s-+\\(\\sw*\\|\\[\\(\\s-*\\sw+\\s-*\\)\\]\\)[ \t\n]*::?=[ \t\n]*\\(\\(\_\_[^_]+\_\_\\|[^|][^(|]+\\)\\s-*\\(\(.*\)\\)?\\)"
     (2 (symbol-value 'dol-other-name-face) keep t)
     (4 (symbol-value 'dol-other-name-face) keep t)
     (6 (symbol-value 'dol-other-name-face) keep t))
   ;; constructor
   '("\|\\s-+\\(\_\_[^|_]+\_\_\\|[^|][^(|]+\\)\\s-*\\(\([^|]+\)\\)?[ \t\n]*"
     (1 (symbol-value 'dol-other-name-face) keep t))
   ;; in ()1
   '("\(\\(\\(\\sw\\|,\\)*\\)\\s-*:\\??[^)]*\)"
     (1 (symbol-value 'dol-other-name-face) keep t))
   ;; in ()2
   '("\([^;]*;\\s-*\\(\\sw+\\)\\s-*:\\??.*\)"
     (1 (symbol-value 'dol-other-name-face) keep t))
   ))
   "Reserved keywords highlighting")

;; String and Char
(defconst dol-font-lock-string
  (append dol-font-lock-keywords
	  (list '("\\(\\(\"\\|^>[ \t]*\\\\\\)\\([^\"\\\\\n]\\|\\\\.\\)*\\(\"\\|\\\\[ \t]*$\\)\\|'\\([^'\\\\\n]\\|\\\\.[^'\n]*\\)'\\)"
		  (0 (symbol-value 'dol-string-char-face) keep t))
	  ))
  "Syntax highlighting of String and Char")

;; Define default highlighting level
;; (defvar dol-font-lock-syntax-highligthing dol-font-lock-keywords
(defvar dol-font-lock-syntax-highligthing (symbol-value 'dol-font-lock-string)
  "Default syntax highlighting level in DOL mode")

;; ======================= R U N   H E T S =======================
(require 'compile)

(setq dol-error-list nil)
(defvar hets-program nil)
(defvar old-buffer nil)
(defvar dol-hets-options nil
  "*the additional options for running hets.")

(defun dol-run-hets (&rest opt)
  "Run hets process to compile the current DOL file."
  (interactive)
  (save-buffer nil)
  (setq old-buffer (current-buffer))
  (let* ((run-option " ")
	 (dol-hets-file-name (buffer-file-name))
	 (outbuf (get-buffer-create "*hets-run*")))
    (if hets-program
	(setq dol-hets-program hets-program)
      (setq dol-hets-program "hets"))
    (if opt
	(dolist (current opt run-option)
	  (setq run-option (concat run-option current " "))))
    (setq hets-command (concat dol-hets-program run-option "\"" dol-hets-file-name "\""))

    ;; Pop up the compilation buffer.
    (set-buffer outbuf)
    (setq buffer-read-only nil)
    (buffer-disable-undo (current-buffer))
    (erase-buffer)
    (buffer-enable-undo (current-buffer))
    (set-buffer-modified-p nil)
    (insert hets-command "\n")
    (pop-to-buffer outbuf)
    (goto-char (point-max))
    ;; (display-buffer outbuf nil t)
    (save-excursion
      ;; (set-buffer outbuf)
      (compilation-mode "hets-compile")
      ;; Start the compilation.
      (if (fboundp 'start-process)
	  (let* ((process-environment
		  (append
		   (if (and (boundp 'system-uses-terminfo)
			    system-uses-terminfo)
		       (list "TERM=dumb" "TERMCAP="
			     (format "COLUMNS=%d" (window-width)))
		     (list "TERM=emacs"
			   (format "TERMCAP=emacs:co#%d:tc=unknown:"
				   (window-width))))
		   ;; Set the EMACS variable, but
		   ;; don't override users' setting of $EMACS.
		   (if (getenv "EMACS")
		       process-environment
		     (cons "EMACS=t" process-environment))))
		 (proc (start-process-shell-command "hets-compile" outbuf
						    hets-command)))
	    (setq buffer-read-only nil)
	    (set-process-sentinel proc 'dol-compilation-sentinel)
	    (set-process-filter proc 'dol-compilation-filter)

	    (set-marker (process-mark proc) (point) outbuf))
	))
      (pop-to-buffer old-buffer)))

(defun dol-run-hets-r (&rest opt)
  "Run hets process with options (from dol-hets-options) to compile the
   current DOL file."
  (interactive)
  (setq option1 nil)
  (setq option2 nil)
  (setq run-option-r nil)
  (if dol-hets-options
      (setq run-option-r dol-hets-options))
  (if opt
      (dolist (current opt option2)
	(setq option2 (concat option2 current " ")))
    )
  (setq run-option-r (concat run-option-r " " option2))
  (dol-run-hets run-option-r)
)

(defun dol-run-hets-g ()
  "Run hets process with -g and other options (from variable dol-hets-options)
   to compile the current DOL file."
  (interactive)
  (dol-run-hets-r "-g")
)

;; sentinel and filter of asynchronous process of hets
;; Called when compilation process changes state.
(defun dol-compilation-sentinel (proc msg)
  "Sentinel for compilation buffers."
  (let ((buffer (process-buffer proc)))
    (if (memq (process-status proc) '(signal exit))
	(progn
	  (if (null (buffer-name buffer))
	      ;; buffer killed
	      (set-process-buffer proc nil)
	    (let ((obuf (current-buffer)))
	      ;; save-excursion isn't the right thing if
	      ;; process-buffer is current-buffer
	      (unwind-protect
		  (progn
		    ;; Write something in the compilation buffer
		    ;; and hack its mode line.
		    (set-buffer buffer)
		    (dol-compilation-handle-exit (process-status proc)
					     (process-exit-status proc)
					     msg)
		    ;; Since the buffer and mode line will show that the
		    ;; process is dead, we can delete it now.  Otherwise it
		    ;; will stay around until M-x list-processes.
		    (delete-process proc))
		(set-buffer obuf))))
	  ;; (setq compilation-in-progress (delq proc compilation-in-progress))
	  ))))

;; show the message from hets compile direct on *hets-run* buffer
(defun dol-compilation-filter (proc string)
  (display-buffer (process-buffer proc))
  (unless (equal (buffer-name) "*hets-run*")
    (progn
      (pop-to-buffer "*hets-run*")
      (goto-char (point-max))
      ))
  (with-current-buffer (process-buffer proc)
    (let ((moving (= (point) (process-mark proc))))
      (save-excursion
        ;; Insert the text, advancing the process marker.
        (goto-char (process-mark proc))
        (insert string)

        (set-marker (process-mark proc) (point)))
      (if moving (goto-char (process-mark proc)))))
  (pop-to-buffer old-buffer))

(defun dol-compilation-handle-exit (process-status exit-status msg)
  "Write msg in the current buffer and hack its mode-line-process."
  (let ((buffer-read-only nil)
	(status (cons msg exit-status))
	(omax (point-max))
	(opoint (point)))
    ;; Record where we put the message, so we can ignore it
    ;; later on.
    ;; (goto-char omax)
    (goto-char (point-max))
    (insert ?\n mode-name " " (car status))
    (if (bolp)
	(forward-char -1))
    (insert " at " (substring (current-time-string) 0 19))
    (goto-char (point-max))
    (setq mode-line-process (format ":%s [%s]" process-status (cdr status)))
    ;; Force mode line redisplay soon.
    (force-mode-line-update)
    (if (and opoint (< opoint omax))
	(goto-char opoint))

    ;; Automatically parse (and mouse-highlight) error messages:
    (if (zerop exit-status)
	(setq dol-error-list nil)
      (setq dol-error-list nil)
      (dol-parse-error)
      (message "%s errors have been found." (length dol-error-list)))
    (pop-to-buffer old-buffer)
    ))

;; also functions with old hets-program?
(defun dol-parse-error ()
  "Error Parser"
  (interactive)
  (setq dol-error-list nil)
  ;;;(pop-to-buffer compiler-buffer)
  (pop-to-buffer "*hets-run*")
  (goto-char (point-min))
  (while (not (eobp))
    (if (not (or (looking-at "Fail") (and (looking-at "\\*\\*\\*") (looking-at "[0-9]+\\.[0-9]+-[0-9]+\\.[0-9]*"))))
	(forward-line 1)
      (skip-chars-forward "a-zA-Z*,/._\\- ")
      (if (not (search-forward ":" (save-excursion (end-of-line) (point)) t 1))
	  (forward-line 1)
	(re-search-backward "\\(\(\\|\\s-+\\)\\([^.]+\\.\\(dol\\|het\\)\\)" nil t 1)
	(setq file-name (match-string-no-properties 2))
	(re-search-forward ":\\([0-9]+\\)\\.\\([0-9]+\\)\\(-[0-9]+\\.[0-9]*\\)?[:,]" (save-excursion (end-of-line) (point)) t 1)
	(when (not (string= (match-string-no-properties  0) ""))
	  (setq error-line (match-string-no-properties 1))
	  (setq error-colnum (match-string-no-properties 2))
	  (setq error-window-point (point))
	  (setq dol-error-list
		(nconc dol-error-list (list (list file-name error-line error-colnum error-window-point))))
	)
	(forward-line 1)))))

(defun dol-compile-goto-next-error ()
  "search the next error position from error-list, and move to it."
  (interactive)
  ;; if error-list is empty ...
  (if (null dol-error-list)
      (dol-parse-error))
  (if (null dol-error-list)
      (if (member (get-buffer "*hets-run*") (buffer-list))
	  (message "no error.")
	(message "this file have not yet been compiled."))
    (let* ((this-error (pop dol-error-list))
	   (error-file-name (nth 0 this-error))
	   (error-line (nth 1 this-error))
	   (error-column (nth 2 this-error))
	   (error-window-point (nth 3 this-error)))

      ;; (message "DEBUG<Goto Error>: file: %s, line: %s, column: %s" error-file-name  error-line error-column)
      ;; if the file already opened ...
      (if (get-file-buffer error-file-name)
	  (pop-to-buffer (get-file-buffer error-file-name))
	(generate-new-buffer error-file-name)
	(pop-to-buffer error-file-name)
	(insert-file-contents error-file-name))
      ;; switch to hets-run window to jump to next error message
      (setq file-buffer (current-buffer))
      (pop-to-buffer "*hets-run*")
      (goto-char error-window-point)
      ;; return to current file
      (pop-to-buffer file-buffer)
      (goto-line (string-to-number error-line))
      (move-to-column (- (string-to-number error-column) 1))
      (message "goto next error... line: %s column: %s" error-line error-column)
      (setq dol-error-list (nconc dol-error-list (list this-error)))
      )))

;; ================= D O L   M A J O R   M O D E ===============
;; dol major mode setup
;; Definition of DOL major mode
(defun dol-mode ()
  "Major mode for editing DOL models"
  (interactive)
  (dol-vars)
  (setq major-mode 'dol-mode)
  (setq mode-name "DOL")
  ;; Load keymap
  (use-local-map dol-mode-map)
  ;; Load syntax table
  (set-syntax-table dol-mode-syntax-table)
  ;; (dol-create-syntax-table)
  ;; Highlight DOL keywords
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults
	'(dol-font-lock-syntax-highligthing))
  (make-local-variable 'font-lock-keywords-only)
  (setq font-lock-keywords-only nil)
  ;; Support for compile.el
  ;; We just substitute our own functions to go to the error.
  (add-hook 'compilation-mode-hook
            (lambda()
	      (set (make-local-variable 'compile-auto-highlight) 40)
	      ;; FIXME: This has global impact!  -stef
	      (define-key compilation-minor-mode-map [mouse-2]
		'dol-compile-mouse-goto-error)
	      (define-key compilation-minor-mode-map "\C-m"
		'dol-compile-goto-next-error)))
  (run-hooks 'dol-mode-hook)
  )

(provide 'dol-mode)

;; DOL-mode ends here
