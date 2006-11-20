;; Files whose extension is .casl or .het will be edited in CASL mode
(setq hets-program "/home/jiang/CASL/HetCATS/hets")
(setq load-path
      (append '("/home/jiang/CASL/HetCATS/utils/el") load-path))
(setq auto-mode-alist
      (append
       '(("\\.casl\\'" . casl-mode))
       '(("\\.het\\'"  . casl-mode))
       auto-mode-alist))
