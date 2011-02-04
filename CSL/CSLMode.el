;; Creating a new menu pane in the menu bar to the right of "Tools" menu
;; A keymap is suitable for menu use if it has an overall prompt string, which describes the purpose of the menu.
;; essentially: define-key map fake-key '(item command), where fake-key is of the form [menu-bar mymenu nl] and defines key nl in mymenu which must exist

(define-key-after
  global-map
  [menu-bar enclmenu]
  (cons "ENCL" (make-sparse-keymap "encl menu"))
  'tools)


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
	  (push (buffer-substring-no-properties p1 (point)) specs)
	  (skip-chars-forward " ")
	  )
	)
      specs
      )
    )
  )

(defun refresh-specmenu ()
  (interactive)
  (let
      ((entries (sort (append (extractspecs) (extractgets)) 'string<))
       currentsym
       )    
    
    ;; delete the match menu
    (global-unset-key [menu-bar enclmenu match])
    ;; generate match menu
    (define-key-after global-map [menu-bar enclmenu match] (cons "Match" (make-sparse-keymap)) 'kill-buffer)
    
    ;; generate subentries  
    (dolist (item entries)
      (setq currentsym (gensym))
      (define-key global-map (vector 'menu-bar 'enclmenu 'match currentsym) (cons item (make-sparse-keymap)))
      ;; submenus
      (dolist (item2 entries)
	(setq currentsym2 (gensym))
	(define-key global-map (vector 'menu-bar 'enclmenu 'match currentsym currentsym2) (cons item2 (make-sparse-keymap)))
	(dolist (item3 '("Show match" "Export parameter"))
	(define-key global-map (vector 'menu-bar 'enclmenu 'match currentsym currentsym2 (gensym))
	  (cons item3 `(lambda () (interactive) (run-csl ,item ,item2 ,item3))))
	)

	)
    (define-key global-map (vector 'menu-bar 'enclmenu 'match currentsym (gensym)) (cons "--" nil))
    (define-key global-map (vector 'menu-bar 'enclmenu 'match currentsym (gensym)) (cons "Select design spec" nil))

      )
    (define-key global-map (vector 'menu-bar 'enclmenu 'match (gensym)) (cons "--" nil))
    (define-key global-map (vector 'menu-bar 'enclmenu 'match (gensym)) (cons "Select pattern spec" nil))
    )
  )

(defun run-csl (spec1 spec2 trans)
  (interactive)
;;  (message "selected %s and %s and %s" spec1 spec2 trans)
;; example command
;; matchcad /tmp/flange.het -sMatch -pFlangePattern -dComponent
;  (message (concatenate 'string "asd" (buffer-file-name (current-buffer))))
;  (call-process "/bin/ls" nil (get-buffer-create "*Match-Result*") t "-lh" "/tmp/")

 
  (call-process "matchcad" nil (get-buffer-create "*Match-Result*") t
		"-sMatch"
		"-p" spec1
		"-d" spec2
		(if (string= trans "Show match") "" "-t")
		(buffer-file-name (current-buffer)))

  (switch-to-buffer (get-buffer "*Match-Result*"))
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
