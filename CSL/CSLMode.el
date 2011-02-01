;; Creating a new menu pane in the menu bar to the right of "Tools" menu
;; A keymap is suitable for menu use if it has an overall prompt string, which describes the purpose of the menu.
;; essentially: define-key map fake-key '(item command), where fake-key is of the form [menu-bar mymenu nl] and defines key nl in mymenu which must exist

(define-key-after
  global-map
  [menu-bar enclmenu]
  (cons "ENCL" (make-sparse-keymap "encl menu"))
  'tools)

(define-key-after global-map [menu-bar enclmenu match] 
  (cons "Match" (make-sparse-keymap "major modes")) 'kill-buffer )

(define-key global-map [menu-bar enclmenu match others] '("..." . nil))
(define-key global-map [menu-bar enclmenu match abstractflange] '("Abstract Flange" . match-abstractflange))

(defun match-abstractflange ()
  (interactive)
  (message "buffer name is %s" (buffer-file-name (current-buffer)))
  (call-process "/bin/ls" nil (get-buffer-create "*Match-Result*") t)
  (switch-to-buffer (get-buffer "*Match-Result*"))
  )

