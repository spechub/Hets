
;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) University of Magdeburg, 2007-2016
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dol-mode-directory-fn ()
  "Used to find dol-mode directory"
  (let ((curdir 
	 (or
	  (and load-in-progress (file-name-directory load-file-name))
	  (file-name-directory (buffer-file-name)))))
    (file-name-directory curdir))  
)

(setq dol-mode-directory (dol-mode-directory-fn))
(let ((hets-base-dir (expand-file-name 
		     (concat dol-mode-directory "../.."))))
  (if (file-executable-p (concat hets-base-dir "/hets"))
	(setq hets-program (concat hets-base-dir "/hets"))
    (progn
      (if (file-executable-p (concat hets-base-dir "/bin/hets"))
	  (setq hets-program (concat hets-base-dir "/bin/hets"))
	(progn
	  (message (concat "no hets found in " hets-base-dir)))
	)
      )
    )
)

(add-to-list 'load-path dol-mode-directory)
;; Files whose extension is .dol or .het will be edited in DOL mode
(setq auto-mode-alist
      (append
       '(("\\.dol\\'" . dol-mode))
       '(("\\.het\\'"  . dol-mode))
       '(("\\.clif\\'"  . dol-mode))
       '(("\\.casl\\'"  . dol-mode))
       auto-mode-alist))
(autoload 'dol-mode "dol-mode" "Entering DOL mode..." t)
(add-hook 'dol-mode-hook 'turn-on-dol-indent)
(message "dol-mode setup complete")
