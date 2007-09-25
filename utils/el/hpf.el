
;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) Heng Jiang, Uni Bremen 2007
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hpf-mode-directory-fn ()
  "Used to find hpf-mode directory"
  (let ((curdir 
	 (or
	  (and load-in-progress (file-name-directory load-file-name))
	  (file-name-directory (buffer-file-name)))))
    (file-name-directory curdir))  
)

(setq hpf-mode-directory (hpf-mode-directory-fn))

(add-to-list 'load-path hpf-mode-directory)
;; Files whose extension is .hpf or .het will be edited in HPF mode
(setq auto-mode-alist
      (append
       '(("\\.hpf\\'"  . hpf-mode))
       auto-mode-alist))
(autoload 'hpf-mode "hpf-mode" "Entering HPF mode..." t)
(message "hpf-mode setup complete")
