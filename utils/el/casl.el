(defun hets-home-directory-fn ()
  "Used to find hets-home-directory"
  (let ((curdir 
	 (or
	  (and load-in-progress (file-name-directory load-file-name))
	  (file-name-directory (buffer-file-name)))))
    (file-name-directory (substring curdir 0 -9)))  
)

;; Files whose extension is .casl or .het will be edited in CASL mode
(setq hets-home-directory (hets-home-directory-fn))
(setq hets-program (concat hets-home-directory "hets"))
(setq load-path
      (append (list (concat hets-home-directory "utils/el")) load-path))
(setq auto-mode-alist
      (append
       '(("\\.casl\\'" . casl-mode))
       '(("\\.het\\'"  . casl-mode))
       auto-mode-alist))
