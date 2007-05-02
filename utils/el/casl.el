
;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) Heng Jiang, Klaus Lüttich, Uni Bremen 2007
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun casl-mode-directory-fn ()
  "Used to find casl-mode directory"
  (let ((curdir 
	 (or
	  (and load-in-progress (file-name-directory load-file-name))
	  (file-name-directory (buffer-file-name)))))
    (file-name-directory curdir))  
)

(setq casl-mode-directory (casl-mode-directory-fn))
(let ((hets-base-dir (expand-file-name 
		     (concat casl-mode-directory "../.."))))
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

(add-to-list 'load-path casl-mode-directory)
;; Files whose extension is .casl or .het will be edited in CASL mode
(setq auto-mode-alist
      (append
       '(("\\.casl\\'" . casl-mode))
       '(("\\.het\\'"  . casl-mode))
       auto-mode-alist))
(autoload 'casl-mode "casl-mode" "Entering CASL mode..." t)
(add-hook 'casl-mode-hook 'turn-on-casl-indent)
(message "casl-mode setup complete")
