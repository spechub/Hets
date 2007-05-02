;;;###autoload
(autoload 'turn-on-casl-indent "casl-indent" "Turn on CASL indentation." t)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) Heng Jiang, Klaus Lüttich, Uni Bremen 2007
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Version number
(defconst casl-mode-version "0.4"
  "Version of CASL-Mode")

(defgroup casl nil
  "Major mode for editing (heterogeneous) CASL specifications."
  :group 'languages
  :prefix "casl-")

(defvar casl-mode-hook nil)
(defvar casl-mode-map (let ((keymap (make-keymap)))
			(define-key keymap "\C-c\C-c" 'comment-region)
			(define-key keymap "\C-c\C-r" 'casl-run-hets-r)
			(define-key keymap "\C-c\C-g" 'casl-run-hets-g)
			(define-key keymap "\C-c\C-n" 'casl-compile-goto-next-error)
			keymap) 
  "Keymap for CASL major mode")

;; Are we running FSF Emacs or XEmacs?
(defvar casl-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

;; ====================== S Y N T A X   T A B L E ==================
;; Syntax table for CASL major mode
(defvar casl-mode-syntax-table nil
  "Syntax table for CASL mode.")

(if casl-mode-syntax-table
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
    (setq casl-mode-syntax-table table))
  )

;; Various mode variables.
(defun casl-vars ()
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
  (setq comment-indent-function 'casl-comment-indent)
  (make-local-variable 'comment-end)
  (setq comment-end "]%")
  (set (make-local-variable 'comment-end-skip) "[\]}]%")
)

;; Find the indentation level for a comment.
(defun casl-comment-indent ()
  (skip-chars-backward " \t")
  ;; if the line is blank, put the comment at the beginning,
  ;; else at comment-column
  (if (bolp) 0 (max (1+ (current-column)) comment-column)))

;; ============= K E Y W O R D   H I G H L I G H T I N G ============
(defface casl-black-komma-face
  `((t (:foreground "black")))
  ""
  :group 'basic-faces)
(defvar casl-black-komma-face 'casl-black-komma-face
  "Face name to use for black komma.")

(defvar  casl-annotation-face 'casl-annotation-face
   "CASL mode face for Annotations")
(setq casl-annotation-face 'font-lock-constant-face)

(defvar casl-name-face 'casl-name-face)
(setq casl-name-face 'font-lock-variable-name-face)

(defvar casl-keyword-face 'casl-keyword-face)
(setq casl-keyword-face 'font-lock-keyword-face)

(defvar casl-library-name-face 'casl-library-name-face)
(setq casl-library-name-face 'font-lock-type-face)

(defvar casl-builtin-face 'casl-builtin-face)
(setq casl-builtin-face 'font-lock-builtin-face)

(defvar casl-comment-face 'casl-comment-face)
(setq casl-comment-face 'font-lock-comment-face)

(defvar casl-other-name-face 'casl-other-name-face)
(setq casl-other-name-face 'font-lock-function-name-face)

(defvar casl-string-char-face 'casl-string-char-face)
(setq casl-string-char-face 'font-lock-string-face)

;; Syntax highlighting of CASL
;; "Warning: Do not design an element of font-lock-keywords to match 
;;  text which spans lines; this does not work reliably. While 
;;  font-lock-fontify-buffer handles multi-line patterns correctly, 
;;  updating when you edit the buffer does not, since it considers 
;;  text one line at a time." (from the GNU Emacs Lisp Reference Manual)

;; order of all the following highlighting rules is significant,
;; ony change if really needed

 ;; Comment
(defconst casl-font-lock-specialcomment
	 (list    
	  '("%%.*$" (0 (symbol-value 'casl-comment-face) keep t)))
	 "Special Comment")

;; Alternativ for Annotation
(defconst casl-font-lock-annotations
  (append casl-font-lock-specialcomment
	  (list 
	   ;; always highlight closing )%
	   '("\\(\)%\\)[^%]" (1 (symbol-value 'casl-annotation-face) keep t))
	   ;; %words \n
	   '("%\\w+\\b[^\n]*$" (0 (symbol-value 'casl-annotation-face) keep t))
	   ;; %(.....)%
	   '("[^%]\\(%\([^)]*?\)%\\)[^%]" (1 (symbol-value 'casl-annotation-face) keep t)) 
	   ;; %word( ... )%
	   '("\\(%\\sw+\([^)]*?\)%\\)[^%]" (1 (symbol-value 'casl-annotation-face) keep t))
	   ))
  "Annotation")

(defconst casl-font-lock-keywords
 (append casl-font-lock-annotations 
  (list
   ;; reserved keyword
   '("\\(\\<\\|\\s-+\\)\\(/\\\\\\|\\\\/\\|=>\\|<=>\\|and\\|axioms?\\|arch\\|assoc\\|behaviourally\\|closed\\|comm\\|else\\|end\\|exists!?\\|fit\\|forall\\|free\\|generated\\|given\\|hide\\|idem\\|if\\|local\\|not\\|refined\\|refinement\\|reveal\\|spec\\|then\\|to\\|unit\\|via\\|view\\|when\\|within\\|with\\|\\(\\(op\\|pred\\|var\\|type\\|sort\\)s?\\)\\)\\(\\b\\|[ \t\n]\\)"  
     (2 (symbol-value 'casl-keyword-face) keep t))
   ;; delimiters always in black after this
   '("\\([,;.()]\\|::?=\\)\\|[^:]\\(:\\)[^:]" 
     (1 (symbol-value 'casl-black-komma-face) keep t) (2 (symbol-value 'casl-black-komma-face) keep t))
   ;; after forall don't highlight
   '("\\<\\(forall\\|exists\\)\\>\\(.+\\)"
     (2 (symbol-value 'casl-black-komma-face) keep t))
   ;; between a descrete : and a descrete ; always in Black
   '("[^:]:\\([^:][^;]+?\\);[^;]"
      (1 (symbol-value 'casl-black-komma-face) keep t))
   ;; Keywords of loading Library 
   '("\\b\\(logic\\|from\\|get\\|library\\|version\\)\\b"  
     (1 (symbol-value 'casl-builtin-face) keep t))
   ;; library versions
   '("\\b\\(version\\)\\b[ \t]+\\([0-9.]+\\)" 
       (2 (symbol-value 'casl-black-komma-face) keep t))
   ;; = { <up to> : <sort> . always black
   '("=[ \t\n]*{[^:]+:[^.]+\\." (0 (symbol-value 'casl-black-komma-face) keep t))
   ;; (var:<sort>) always black
   '("\\(\([^)]+?\)\\)[ \t\n]*\\(<=>\\|:\\)" (1 (symbol-value 'casl-black-komma-face) keep t))
   ;; Library and Logic name
   '("\\b\\(library\\|logic\\)\\s-+\\(\\(\\w\\|/\\)+\\)\\b"  
     (2 (symbol-value 'casl-library-name-face) keep t))
   ;; name of get
   '("\\b\\(get\\)[ \t\n]\\([_A-Za-zäöüÄÖÜß,\t\n ]+\\)\\(from\\|spec\\|unit\\|arch\\|view\\|logic\\|%[\\[{(\\w]\\|$\\)"  
     (2 (symbol-value 'casl-name-face) keep t))
   ;; library name in from
   '("\\bfrom[ \t]+\\(.+?\\)\\(get\\|$\\)" 
     (1 (symbol-value 'casl-library-name-face) keep t))
   ;; then, and + name
   '("\\(\\<\\|\\s-+\\)\\(and\\|then\\)[ \t\n]*\\([A-Z]\\w*\\)\\s-*\\(\\[\\([A-Z]\\sw*\\).*\\]\\)?" 
     (3 (symbol-value 'casl-name-face) keep t) (5 (symbol-value 'casl-name-face) keep t))
   ;; names before and after to 
   '("[ \t\n]*\\(\\sw+\\)[ \t\n]+to[ \t\n]+\\(\\(\\sw+\\)\\s-*\\(\\[\\([A-Z]\\sw*\\).*\\]\\)?[, \t]*\\)?" 
     (1 (symbol-value 'casl-name-face) keep t) (3 (symbol-value 'casl-name-face) keep t) (5 (symbol-value 'casl-name-face) keep t))
   ;; instance name of specification 
   '("\\<spec.+=\\s-*\\(%\\sw+\\s-*\\)?[ \t\n]*\\([A-Z]\\w*\\)\\s-*\\(\\[\\s-*\\([A-Z]\\w*\\).*\\s-*\\]\\)?"
     (2 (symbol-value 'casl-name-face) keep t) (4 (symbol-value 'casl-name-face) keep t))
   ;; the name of a specification 
   '("\\b\\(spec\\)\\([^=\n]+?\\)\\(\\[\\|=\\|$\\)"
     (2 (symbol-value 'casl-name-face) keep t))
   ;; the name of a view
   '("\\b\\(view\\)\\([^:\n]+?\\)\\(\\]\\|\\[\\|:\\|$\\)"
     (2 (symbol-value 'casl-name-face) keep t))
   ;; Basic signature: sort X, Y, Z  
   '("\\bsorts?[ \t]+\\(\\(<?[^<]*?\\|\\[[^\\]]+?\\]\\)+\\)\\($\\|=\\|\\]\\||->\\)" 
     (1 (symbol-value 'casl-other-name-face) keep t))
   ;; Basic signature: op ,pred and var name
   '("\\(\\<[0-9]\\|\\w[^()\n]*?[^:]\\|\\w\\):\\??[ \nA-Za-zäöüÄÖÜß{}]"
      (1 (symbol-value 'casl-other-name-face) keep t))
   '("\\(\\<\\w[^()\n]*?[^(]\\|\\w\\)\([^):]+?:"
      (1 (symbol-value 'casl-other-name-face) keep t))
   ;; highlight a line with , at end
   '("^\\(\\(\\(__\\s-*[^_\n]+\\s-*__\\|[^.,:>\n]+\\)\\s-*,\\s-*\\)+\\)$"
     (0 (symbol-value 'casl-other-name-face) keep t))
   ;; names before and after '|->'
   '("[ \t\n]*\\(__[^|_]+__\\|[^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[ \t\n]*|->[ \t\n]*\\(__[^|_]+__\\|[^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[, \t]*" 
     (1 (symbol-value 'casl-other-name-face) keep t) (3 (symbol-value 'casl-other-name-face) keep t) 
     (4 (symbol-value 'casl-other-name-face) keep t) (6 (symbol-value 'casl-other-name-face) keep t)) 
   ;; type name and first alternative
    '("\\btype\\b\\([^:]+\\)::?=\\([^|(]+\\)\\(|\\|(\\|$\\)"
     (1 (symbol-value 'casl-other-name-face) keep t) (2 (symbol-value 'casl-other-name-face) keep t))
   ;; from here on everything in parens in black and =
   '("\\[.*?\\]\\|{.*?}\\|=" (0 (symbol-value 'casl-black-komma-face) keep t))
   ;; name of given
   '("\\b\\(given\\)[ \t\n]+\\(.*?\\)\\(=\\|:\\|$\\)"  
     (2 (symbol-value 'casl-name-face) keep t))
   ;; constructor
   '("\|\\s-+\\(\_\_[^|_]+\_\_\\|[^|][^(|]+\\)\\s-*\\(\([^|]+\)\\)?[ \t\n]*"
     (1 (symbol-value 'casl-other-name-face) keep t))
   ;; in ()1
   '("\(\\(\\(\\sw\\|,\\)*\\)\\s-*:\\??[^):]*\)"
     (1 (symbol-value 'casl-other-name-face) keep t))
   ;; in ()2+
   '("\([^;]*\\(;\\s-*\\(\\sw+\\)\\s-*:\\??.*?\\)+\)"
     (2 (symbol-value 'casl-other-name-face) keep t) (4 (symbol-value 'casl-other-name-face) keep t))
  ))
  "Reserved keywords highlighting")

;; String and Char
(defconst casl-font-lock-string
  (append casl-font-lock-keywords
	  (list '("\\(\\(\"\\|^>[ \t]*\\\\\\)\\([^\"\\\\\n]\\|\\\\.\\)*\\(\"\\|\\\\[ \t]*$\\)\\|'\\([^'\\\\\n]\\|\\\\.[^'\n]*\\)'\\)" (0 (symbol-value 'casl-string-char-face) keep t))
	  ))
  "Syntax highlighting of String and Char") 

;; Define default highlighting level
;; (defvar casl-font-lock-syntax-highligthing casl-font-lock-keywords
(defvar casl-font-lock-syntax-highligthing (symbol-value 'casl-font-lock-string)
  "Default syntax highlighting level in CASL mode")

;; ======================= R U N   H E T S =======================
(require 'compile)

(setq casl-error-list nil)
(defvar hets-program nil)
(defvar old-buffer nil)
(defvar casl-hets-options nil
  "*the additional options for running hets.")

(defun casl-run-hets (&rest opt)
  "Run hets process to compile the current CASL file."
  (interactive)
  (save-buffer nil)
  (setq old-buffer (current-buffer))
  (let* ((run-option " ")
	 (casl-hets-file-name (buffer-file-name))
	 (outbuf (get-buffer-create "*hets-run*")))
    (if hets-program 
	(setq casl-hets-program hets-program)
      (setq casl-hets-program "hets"))
    (if opt
	(dolist (current opt run-option)
	  (setq run-option (concat run-option current " "))))
    (setq hets-command (concat casl-hets-program run-option casl-hets-file-name))

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
	    (set-process-sentinel proc 'casl-compilation-sentinel)
	    (set-process-filter proc 'casl-compilation-filter)
	    
	    (set-marker (process-mark proc) (point) outbuf))
	))
      (pop-to-buffer old-buffer)))

(defun casl-run-hets-r (&rest opt)
  "Run hets process with options (from casl-hets-options) to compile the 
   current CASL file."
  (interactive)
  (setq option1 nil)
  (setq option2 nil)
  (setq run-option-r nil)
  (if casl-hets-options
      (setq run-option-r casl-hets-options))
  (if opt
      (dolist (current opt option2)
	(setq option2 (concat option2 current " ")))
    )
  (setq run-option-r (concat run-option-r " " option2))
  (casl-run-hets run-option-r)
)

(defun casl-run-hets-g ()
  "Run hets process with -g and other options (from variable casl-hets-options)
   to compile the current CASL file."
  (interactive)
  (casl-run-hets-r "-g")
)

;; sentinel and filter of asynchronous process of hets
;; Called when compilation process changes state.
(defun casl-compilation-sentinel (proc msg)
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
		    (casl-compilation-handle-exit (process-status proc)
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
(defun casl-compilation-filter (proc string)
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

(defun casl-compilation-handle-exit (process-status exit-status msg)
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
	(setq casl-error-list nil)
      (setq casl-error-list nil)
      (casl-parse-error)
      (message "%s errors have been found." (length casl-error-list)))
    (pop-to-buffer old-buffer)
    ))

;; also functions with old hets-program?
(defun casl-parse-error ()
  "Error Parser"
  (interactive)
  (setq casl-error-list nil)
  ;;;(pop-to-buffer compiler-buffer)
  (pop-to-buffer "*hets-run*")
  (goto-char (point-min))
  (while (not (eobp))
    (if (not (or (looking-at "Fail") (and (looking-at "\\*\\*\\*") (looking-at "[0-9]+\\.[0-9]+-[0-9]+\\.[0-9]*"))))
	(forward-line 1)
      (skip-chars-forward "a-zA-Z*,/._\\- ")
      (if (not (search-forward ":" (save-excursion (end-of-line) (point)) t 1))
	  (forward-line 1)
	(re-search-backward "\\(\(\\|\\s-+\\)\\([^.]+\\.\\(casl\\|het\\)\\)" nil t 1)
	(setq file-name (match-string-no-properties 2))
	(re-search-forward ":\\([0-9]+\\)\\.\\([0-9]+\\)\\(-[0-9]+\\.[0-9]*\\)?[:,]" (save-excursion (end-of-line) (point)) t 1)
	(when (not (string= (match-string-no-properties  0) ""))
	  (setq error-line (match-string-no-properties 1))
	  (setq error-colnum (match-string-no-properties 2))
	  (setq error-window-point (point))
	  (setq casl-error-list
		(nconc casl-error-list (list (list file-name error-line error-colnum error-window-point))))
	)
	(forward-line 1)))))

(defun casl-compile-goto-next-error ()
  "search the next error position from error-list, and move to it."
  (interactive)
  ;; if error-list is empty ...
  (if (null casl-error-list)
      (casl-parse-error))
  (if (null casl-error-list)
      (if (member (get-buffer "*hets-run*") (buffer-list))
	  (message "no error.")
	(message "this file have not yet been compiled.")) 
    (let* ((this-error (pop casl-error-list))
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
      (setq casl-error-list (nconc casl-error-list (list this-error)))
      )))

;; ================= C A S L   M A J O R   M O D E ===============
;; casl major mode setup
;; Definition of CASL major mode
(defun casl-mode ()
  "Major mode for editing CASL models"
  (interactive)
  (casl-vars)
  (setq major-mode 'casl-mode)
  (setq mode-name "CASL")
  ;; Load keymap
  (use-local-map casl-mode-map)
  ;; Load syntax table
  (set-syntax-table casl-mode-syntax-table)
  ;; (casl-create-syntax-table)
  ;; Highlight CASL keywords
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults
	'(casl-font-lock-syntax-highligthing))
  (make-local-variable 'font-lock-keywords-only)
  (setq font-lock-keywords-only nil)
  ;; Support for compile.el
  ;; We just substitute our own functions to go to the error.
  (add-hook 'compilation-mode-hook
            (lambda()
	      (set (make-local-variable 'compile-auto-highlight) 40)
	      ;; FIXME: This has global impact!  -stef
	      (define-key compilation-minor-mode-map [mouse-2]
		'casl-compile-mouse-goto-error)
	      (define-key compilation-minor-mode-map "\C-m"
		'casl-compile-goto-next-error)))
  (run-hooks 'casl-mode-hook)
  )

(provide 'casl-mode)

;; CASL-mode ends here
