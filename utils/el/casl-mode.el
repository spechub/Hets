;;;###autoload
(autoload 'turn-on-casl-indent "casl-indent" "Turn on CASL indentation." t)

;; Version number
(defconst casl-mode-version "0.2"
  "Version of CASL-Mode")

(defgroup casl nil
  "Major mode for editing (heterogeneous) CASL programs."
  :group 'languages
  :prefix "casl-")

;; casl major mode setup
(defvar casl-mode-hook nil)
(defvar casl-mode-map (let ((keymap (make-keymap)))
			(define-key keymap "\C-c\C-c" 'comment-region)
			(define-key keymap "\C-c\C-r" 'casl-run-hets)
			(define-key keymap "\C-c\C-g" 'casl-run-hetsg)
			(define-key keymap "\C-c\C-n" 'casl-compile-goto-next-error)
			keymap) 
  "Keymap for CASL major mode")

;; Are we running FSF Emacs or XEmacs?
(defvar casl-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

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

(defvar casl-keyword-face 'casl-keyword-face)
(setq casl-keyword-face 'font-lock-keyword-face)

(defvar casl-library-name-face 'casl-library-name-face)
(setq casl-library-name-face 'font-lock-type-face)

(defvar casl-name-face 'casl-name-face)
(setq casl-name-face 'font-lock-variable-name-face)

(defvar casl-builtin-face 'casl-builtin-face)
(setq casl-builtin-face 'font-lock-builtin-face)

(defvar casl-comment-face 'casl-comment-face)
(setq casl-comment-face 'font-lock-comment-face)

(defvar casl-other-name-face 'casl-other-name-face)
(setq casl-other-name-face 'font-lock-function-name-face)

(defvar casl-string-char-face 'casl-string-char-face)
(setq casl-string-char-face 'font-lock-string-face)

;; Syntax highlighting of CASL
(defconst casl-font-lock-keywords
  (list
   ;; Keywords of loading Library 
   '("\\(\\<\\|\\s-+\\)\\(logic\\|from\\|get\\|library\\|version\\)[ :\t\n]+"  
     (2 casl-builtin-face keep t))
;;    '("\\(\\<\\|\\s-+\\)\\(%authors\\|%date\\|%display\\|%prec\\|%left_assoc\\|%number\\|%floating\\|%LATEX\\|%implies\\)[ :\t\n]+"
;;      (2 casl-annotation-face keep t))
   ;; Library and Logic name
   '("\\(\\<\\|\\s-+\\)\\(library\\|logic\\)\\s-+\\(\\(\\w\\|/\\)+\\)[ \t\n]*"  
     (3 casl-library-name-face keep t))
   ;; name of from, get and given
   '("\\(\\<\\|[ \t]+\\)\\(get\\|given\\)[ \t\n]+\\(\\(\\sw+\\s-*\\(,\\|$\\)[ \t\n]*\\)+\\)"  
     (3 casl-name-face keep t))
   '("\\(\\<\\|\\s-+\\)from\\([ \t]+\\)\\(.+\\)\\(get\\|\\s-*\\)" 
     (3 casl-library-name-face keep t))
   ;; the name of specification and view
   '("\\(\\<\\|\\[\\)\\(spec\\|view\\)\\s-+\\(\\w+\\)[ \t]*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?\\s-*.*\\([]=:]\\|::=\\)"
     (3 casl-name-face keep t) (5 casl-name-face keep t))
   ;; then, and + name
   '("\\(\\<\\|\\s-+\\)\\(and\\|then\\)[ \t\n]*\\([A-Z]\\w*\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?" 
     (3 casl-name-face keep t) (5 casl-name-face keep t))
   ;; names before and after to 
   '("[ \t\n]*\\(\\w+\\)[ \t\n]+to[ \t\n]+\\(\\(\\w+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[, \t]*\\)?" 
     (1 casl-name-face keep t) (3 casl-name-face keep t) (5 casl-name-face keep t))
   ;; instance name of specification 
   '("\\<spec.+=\\s-*\\(%\\sw+\\s-*\\)?[ \t\n]*\\([A-Z]\\sw*\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?"
     (2 casl-name-face keep t) (4 casl-name-face keep t))
   ;; Basic signature: sort X, Y, Z  
   '("\\(\\<\\|\\s-+\\)sorts?[ \t]+\\(\\(\\sw+\\s-*\\(\\[\\(\\sw\\|,\\)+\\]\\s-*\\)?\\(,\\(\\s-\\)*\\|$\\|<\\|;\\|=\\)\\(\\sw\\|=\\|<\\|;\\|,\\)*[ \t\n]*\\)+\\)" 
     (2 casl-other-name-face keep t))
   ;; Basic signature: op ,pred and var name
   '("\\(^\\|\\bops?\\|\\bpreds?\\|\\bvars?\\)\\s-+\\([^.]\\(,\\s-*\\)?\\(\\sw\\(,\\s-*\\)?\\|\\(\\s_\\|\\s_+::?\\s_+\\)\\(,\\s-*\\)?\\|\\s(\\|\\s)\\)*\\)\\s-*\\(\(.*\)\\)?\\s-*\\(:\\??\\|<=>\\)[^:\n]*;?[ \t]*$"
     (2 casl-other-name-face keep t))
   ;; type name
   '("\\s-+\\(\\sw+\\)[ \t\n]*::?=\\s-*\\(\\sw*\\).*"
     (1 casl-other-name-face keep t) (2 casl-other-name-face keep t)  )
   ;; constructor
   '("\\(\\sw+\\)?\\s-*|\\s-*\\(\\sw+\\)\\s-*[|(]?\\([ \t\n]*\\|$\\)"
     (1 casl-other-name-face keep t) (2 casl-other-name-face keep t))
   ;; in ()1
   '("\(\\(\\(\\sw\\|,\\)*\\)\\s-*:\\??[^)]*\)"
     (1 casl-other-name-face keep t))
   ;; in ()2
   '("\([^;]*;\\s-*\\(\\sw+\\)\\s-*:\\??.*\)"
     (1 casl-other-name-face keep t))
   ;; names before and after '|->'
   '("[ \t\n]*\\([^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[ \t\n]+|->[ \t\n]+\\([^[ \t\n]+\\)\\s-*\\(\\[\\([A-Z]\\w*\\).*\\]\\)?[, \t]*" 
     (1 casl-other-name-face keep t) (3 casl-other-name-face keep t) 
     (4 casl-other-name-face keep t) (6 casl-other-name-face keep t)) 
   ;; reserved keyword
   '("\\(\\<\\|\\s-+\\)\\(/\\\\\\|\\\\/\\|=>\\|<=>\\|and\\|arch\\|assoc\\|behaviourally\\|closed\\|comm\\|else\\|end\\|exists\\|fit\\|forall\\|free\\|generated\\|given\\|hide\\|idem\\|if\\|local\\|not\\|refined\\|refinement\\|reveal\\|spec\\|then\\|to\\|unit\\|via\\|view\\|when\\|within\\|with\\|\\(\\(op\\|pred\\|var\\|type\\|sort\\)s?\\)\\)[,;]?[ \t\n]"  
     (2 casl-keyword-face keep t))
   '("[,;]" (0 casl-black-komma-face t t))
  )	
  "Reserved keywords highlighting")

;; String and Char
(defconst casl-font-lock-string
  (append casl-font-lock-keywords
	  (list '("\\(\\(\"\\|^>[ \t]*\\\\\\)\\([^\"\\\\\n]\\|\\\\.\\)*\\(\"\\|\\\\[ \t]*$\\)\\|'\\([^'\\\\\n]\\|\\\\.[^'\n]*\\)'\\)" (0 casl-string-char-face t t))
	  ))
  "Syntax highlighting of String and Char") 

;; Alternativ for Annotation
(defconst casl-font-lock-annotations
  (append casl-font-lock-string
	  (list 
	   ;; %word(...)\n
	   '("%\\sw+\([^%\n]+\)$" (0 casl-annotation-face t t))
	   ;; %words \n
	   '("%\\w+[^\n]*$" (0 casl-annotation-face t t))
	   ;; %( ... )% 
	   '("%\([^)%]*\)%[ \t\n]*" (0 casl-annotation-face t t))
	   ;; %word( ... )%
	   '("%\\sw+\([^)%]*\)%[ \t\n]*" (0 casl-annotation-face t t))
	   ))
  "Annotation")

 ;; Comment
(defconst casl-font-lock-specialcomment
  (append casl-font-lock-annotations
	  (list '("\\(%%.*$\\)" (0 casl-comment-face t t))
		'("\\(%{[^}%]*}%\\)[ \t\n]*" (1 casl-comment-face t t))
		))
  "Special Comment")

;; Define default highlighting level
;; (defvar casl-font-lock-syntax-highligthing casl-font-lock-keywords
(defvar casl-font-lock-syntax-highligthing casl-font-lock-specialcomment
  "Default syntax highlighting level in CASL mode")

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
    ;; Commnets
    (if casl-running-xemacs
	((modify-syntax-entry ?% ". 58" table)
	 (modify-syntax-entry ?\[ "(] 6" table)
	 (modify-syntax-entry ?\] ")[ 7" table))
      (modify-syntax-entry ?% ". 14nb" table)
      (modify-syntax-entry ?\[ "(] 2n" table)
      (modify-syntax-entry ?\] ")[ 3n" table))
    ;; commenting-out plus including other kinds of comment
    (modify-syntax-entry ?\( "()" table)
    (modify-syntax-entry ?\) ")(" table)
    (modify-syntax-entry ?{ "(}" table)
    (modify-syntax-entry ?} "){" table)
    (mapcar (lambda (x)
	      (modify-syntax-entry x "_" table))
	    ;; Some of these are actually OK by default.
	    "!#$&*+.,/\\\\:<=>?@^|~")
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
  (setq comment-start-skip "%[%{[] *")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'casl-comment-indent)
  (make-local-variable 'comment-end)
  (setq comment-end "]%"))

;; Find the indentation level for a comment.
(defun casl-comment-indent ()
  (skip-chars-backward " \t")
  ;; if the line is blank, put the comment at the beginning,
  ;; else at comment-column
  (if (bolp) 0 (max (1+ (current-column)) comment-column)))

;; ======================= R U N   H E T S =======================
(require 'compile)
(setq casl-error-list nil)

(defvar hets-program nil)
(defvar old-buffer nil)

(defun casl-run-hets ()
  "Run hets process to compile the current CASL file."
  (interactive)
  (save-buffer nil)
  (setq old-buffer (current-buffer))
  (let* ((casl-hets-file-name (buffer-file-name))
	 (outbuf (get-buffer-create "*hets-run*")))
    (if hets-program 
	(setq casl-hets-program hets-program)
      (setq casl-hets-program "hets"))
    (setq hets-command (concat casl-hets-program " " casl-hets-file-name))

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
	    (set-process-sentinel proc 'casl-compilation-sentinel)
	    (set-process-filter proc 'casl-compilation-filter)
	    
	    (set-marker (process-mark proc) (point) outbuf))
	
        ;; this part is not useful 
	;; force to redisplay

;; 	(message "Executing...")
;; 	(setq mode-line-process ":run")
;; 	(force-mode-line-update)
;; 	(sit-for 0)
;; 	(let ((status 
;; 	       (call-process shell-file-name nil outbuf t "-c" hets-command)))
;; 	  (cond ((numberp status)
;; 		 (casl-compilation-handle-exit 'exit status
;; 					  (if (zerop status)
;; 					      "finished\n"
;; 					    (format "exited abnormally with code %d\n" status))))
;; 		((stringp status)
;; 		 (casl-compilation-handle-exit 'signal status
;; 					  (concat status "\n")))
;; 		(t
;; 		 (casl-compilation-handle-exit 'bizarre status status)))
;; 	  (if (zerop status)
;; 	      (setq casl-error-list nil)
;; 	    (setq casl-error-list nil)
;; 	    (casl-parse-error)
;; 	    (message "%s errors have been found." (length casl-error-list)))
;; 	  )
	))
      (pop-to-buffer old-buffer)))


(defun casl-run-hetsg ()
  "Run hets process with -g to compile the current CASL file."
  (interactive)
  (save-buffer nil)
  (setq old-buffer (current-buffer))
  (let* ((casl-hets-file-name (buffer-file-name))
	 (outbuf (get-buffer-create "*hets-run*")))
    (if hets-program 
	(setq casl-hets-program hets-program)
      (setq casl-hets-program "hets"))
    (setq hets-command (concat casl-hets-program " -g " casl-hets-file-name))

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
      (set-buffer outbuf)
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
	    (set-process-sentinel proc 'casl-compilation-sentinel)
	    (set-process-filter proc 'casl-compilation-filter)
	    
	    (set-marker (process-mark proc) (point) outbuf))
	;; force to redisplay
;; 	(message "Executing...")
;; 	(setq mode-line-process ":run")
;; 	(force-mode-line-update)
;; 	(sit-for 0)
;; 	(let ((status 
;; 	       (call-process shell-file-name nil outbuf t "-c" hets-command)))
;; 	  (cond ((numberp status)
;; 		 (casl-compilation-handle-exit 'exit status
;; 					  (if (zerop status)
;; 					      "finished\n"
;; 					    (format "exited abnormally with code %d\n" status))))
;; 		((stringp status)
;; 		 (casl-compilation-handle-exit 'signal status
;; 					  (concat status "\n")))
;; 		(t
;; 		 (casl-compilation-handle-exit 'bizarre status status)))
;; 	  (if (zerop status)
;; 	      (setq casl-error-list nil)
;; 	    (setq casl-error-list nil)
;; 	    (casl-parse-error)
;; 	    (message "%s errors have been found." (length casl-error-list)))
	  )))
      (pop-to-buffer old-buffer))

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
    (if (not (or (looking-at "Fail") (looking-at "\\*\\*\\*")))
	(forward-line 1)
      (skip-chars-forward "a-zA-Z*,/. ")
      (if (not (search-forward ":" (save-excursion (end-of-line) (point)) t 1))
	  (forward-line 1)
	(re-search-backward "\\(\(\\|\\s-+\\)\\([^.]+\\.\\(casl\\|het\\)\\)" nil t 1)
	(setq file-name (match-string-no-properties 2))
	(re-search-forward ":\\([0-9]+\\)\\.\\([0-9]+\\)[:,]" (save-excursion (end-of-line) (point)) t 1)
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
  (casl-parse-error)
  ;; if error-list is empty ...
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
  ;; Support for compile.el
  ;; We just substitute our own functions to go to the error.
  (add-hook 'compilation-mode-hook
            (lambda()
	      (set (make-local-variable 'compile-auto-highlight) 40)
	      ;; FIXME: This has global impact!  -stef
	      (define-key compilation-minor-mode-map [mouse-2]
		'casl-compile-mouse-goto-error)
	      (define-key compilation-minor-mode-map "\C-m"
		'casl-compile-goto-error)))


  (run-hooks 'casl-mode-hook)
  )

(provide 'casl-mode)

;; CASL-mode ends here
