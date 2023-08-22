;; Creating a new menu pane in the menu bar to the right of "Tools" menu
;; A keymap is suitable for menu use if it has an overall prompt string, which describes the purpose of the menu.
;; essentially: define-key map fake-key '(item command), where fake-key is of the form [menu-bar mymenu nl] and defines key nl in mymenu which must exist

(setq encl-cas "Mathematica")

(setq encl-verb "1")


(define-key-after
  global-map
  [menu-bar enclmenu]
  (cons "EnCL" (make-sparse-keymap "encl menu"))
  'tools)


(define-key-after
  global-map
  [menu-bar enclmenu refresh]
  (cons "Refresh" (make-sparse-keymap)))

(define-key-after
  global-map
  [menu-bar enclmenu refresh matchmenu]
  (cons "Match-menu" `(lambda () (interactive) (refresh-matchmenu))))

(define-key-after
  global-map
  [menu-bar enclmenu refresh evalmenu]
  (cons "Eval-menu" `(lambda () (interactive) (refresh-evalmenu))))


;; extract all spec definitions
(defun extractspecs ()
  (interactive)
  (save-excursion
    (let
	(p1 specs)
      (goto-char (point-min))
      (while (search-forward "spec" nil t)
	(skip-chars-forward " ")
	(setq p1 (point))
	(forward-word)
	(push (buffer-substring-no-properties p1 (point)) specs)
	)
      specs
      )
    )
  )

;; extract all imports
(defun extractgets ()
  (interactive)
  (save-excursion    
    (let
	(p1
	 specs
	 )
      (goto-char (point-min))
      (while (search-forward "get" nil t)
	(skip-chars-forward " ")
	(setq p1 (point))
	(forward-word)
	(push (buffer-substring-no-properties p1 (point)) specs)
	;; comma separated lisp
	(skip-chars-forward " ")
	(while (string= (buffer-substring-no-properties (point) (+ 1 (point))) ",")
	  (skip-chars-forward " ")
	  (setq p1 (+ 1 (point)))
	  (forward-word)
	  (skip-chars-forward " ")
	  (push (buffer-substring-no-properties p1 (point)) specs)
	  (skip-chars-forward " ")
	  )
	)
      specs
      )
    )
  )

(defun refresh-evalmenu ()
  (interactive)
  (let
      ((entries (reverse (sort (append (extractspecs) (extractgets)) 'string<)))
       currentsym
       (menusym 'eval)
       (runfun 'run-eval)
       (runlist '("Symbolic" "Approximately"))
       )
    
    ;; delete the match menu
    (global-unset-key [menu-bar enclmenu eval])
    ;; generate match menu
    (define-key-after global-map [menu-bar enclmenu eval] (cons "Evaluate" (make-sparse-keymap)))

;    (refresh-specmenu entries menusym runfun runlist)

    (dolist (item entries)
    	(setq currentsym (gensym))
    	(define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym) (cons item (make-sparse-keymap)))
    	(dolist (item2 runlist)
    	  (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym (gensym))
    	    (cons item2 `(lambda () (interactive) (,runfun ,item ,item2))))

    	  )

    	)
;    (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym (gensym)) (cons "--" nil))
;    (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym (gensym)) (cons "Select design spec" nil))

    )

  )

(defun refresh-matchmenu ()
  (interactive)
  (let
      ((entries (reverse (sort (append (extractspecs) (extractgets)) 'string<)))
       currentsym
       )
    
    ;; delete the match menu
    (global-unset-key [menu-bar enclmenu match])
    ;; generate match menu
    (define-key-after global-map [menu-bar enclmenu match] (cons "Match" (make-sparse-keymap)) 'kill-buffer)


    (refresh-specmenu entries 'match 'run-match '("Show match" "Export parameter"))
  )
)


(defun refresh-specmenu (entries menusym runfun runlist)
;;  (interactive)
    
    ;; generate subentries  
    (dolist (item entries)
      (setq currentsym (gensym))
      (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym) (cons item (make-sparse-keymap)))
      ;; submenus
      (dolist (item2 entries)
	(setq currentsym2 (gensym))
	(define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym currentsym2) (cons item2 (make-sparse-keymap)))
	(dolist (item3 runlist)
	(define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym currentsym2 (gensym))
	  (cons item3 `(lambda () (interactive) (,runfun ,item ,item2 ,item3))))
	)

	)
    (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym (gensym)) (cons "--" nil))
    (define-key global-map (vector 'menu-bar 'enclmenu menusym currentsym (gensym)) (cons "Select design spec" nil))

      )
    (define-key global-map (vector 'menu-bar 'enclmenu menusym (gensym)) (cons "--" nil))
    (define-key global-map (vector 'menu-bar 'enclmenu menusym (gensym)) (cons "Select pattern spec" nil))
  )


(defun prepare-buffer (name)
  (let ((buff (get-buffer-create name)))
	(with-current-buffer buff (delete-region (point-min) (point-max)))
	buff)
  )

(defun run-match (spec1 spec2 trans)
  (interactive)
  (message "Matching selected pattern with the design spec")
;; example command
;; matchcad /tmp/flange.dol -sMatch -pFlangePattern -dComponent
;  (message (concatenate 'string "asd" (buffer-file-name (current-buffer))))
;  (call-process "/bin/ls" nil (get-buffer-create "*Match-Result*") t "-lh" "/tmp/")

  (call-process "matchcad" nil (prepare-buffer "*Match-Result*") t
		"-sMatch"
		"-p" spec1
		"-d" spec2
		(if (string= trans "Show match") "" "-t")
		(buffer-file-name (current-buffer)))

  (switch-to-buffer (get-buffer "*Match-Result*"))

  (when (string= trans "Export parameter")
    (set-visited-file-name (concatenate 'string (make-temp-file "flangeParams") ".dol"))
    (save-buffer)
    (refresh-evalmenu)
    )
  nil
  )

(defun run-eval (spec1 symbolic)
  (interactive)
;;  (message "selected %s and %s and %s" spec1 spec2 trans)
;; example command
;; matchcad /tmp/flange.dol -sMatch -pFlangePattern -dComponent
;  (message (concatenate 'string "asd" (buffer-file-name (current-buffer))))

;  (message "Evaluating EnCL spec")
  (message "Evaluating EnCL spec %s" spec1)
  (let ((buff (prepare-buffer "*Eval-Result*"))
	(fp (buffer-file-name (current-buffer))))

    (switch-to-buffer buff)
    (insert "Starting evaluation of EnCL specification.\n")
;    (call-process "evalspec" nil buff t "-s" spec1 "-t10" "-v2" (if (string= symbolic "Symbolic") "-S" "") fp)
    (start-process "evaluation of EnCL specification" buff "evalspec" "-C" encl-cas "-s" spec1 "-t25" "-v" encl-verb (if (string= symbolic "Symbolic") "-S" "") fp)
;;    (insert "\n\nEvaluation of EnCL specification finished.\n")
;;    (start-process-shell-command "evalproc" buff (concatenate 'string "evalspec -s " spec1 " " fp))
    nil)
  )

(defun openspec (filename)
  (interactive "FOpen proof script: ")
  filename)


(defun load-spec ()
  (interactive
     (list (call-interactively 'openspec)
       ))

  (refresh-specmenu)
)

(defun setverb0 ()
  (interactive)
  (setq encl-verb "0")
  )
(defun setverb1 ()
  (interactive)
  (setq encl-verb "1")
  )
(defun setverb2 ()
  (interactive)
  (setq encl-verb "2")
  )
(defun setverb3 ()
  (interactive)
  (setq encl-verb "3")
  )

(defun setmaple ()
  (interactive)
  (setq encl-cas "Maple")
  )
(defun setmathematica ()
  (interactive)
  (setq encl-cas "Mathematica")
  )

(setq encl-commands
      '((refresh-evalmenu "Refreshes the EnCL evaluation menu based on the specification in the current buffer.")
	(refresh-matchmenu "Refreshes the EnCL matching menu based on the specification in the current buffer.")
	(setmaple "Selects the computer algebra system Maple for the evaluation.")
	(setmathematica "Selects the computer algebra system Mathematica for the evaluation.")
	(setverbX "Sets verbosity to X in [0-3].")
	(help-encl "Shows this help.")
	)
      )

(defun show-command-entry (x)
  (concatenate 'string (format "%s:\n%s\n" (nth 0 x) (nth 1 x)))
  )

(defun help-encl ()
  (interactive)

  (let ((buff (prepare-buffer "*EnCL-Help*")))

    (switch-to-buffer buff)
    
    (dolist (x encl-commands)
      (insert (show-command-entry x))
      (insert "\n")
      )
    )
  )
