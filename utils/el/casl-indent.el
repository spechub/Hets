
;;;;;;;;;;;;;;;;;;;;;;;;;;
;; $Haeder$
;; Copyright: (c) Heng Jiang, Uni Bremen 2007
;; License: LGPL, see LICENSE.txt or LIZENZ.txt
;; Contact: hets-users@informatik.uni-bremen.de
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; casl-indent.el --- indentation module for CASL Mode
(require 'cl)                           ;need defs of push and pop

(defgroup casl-indent nil
  "casl indentation."
  :group 'casl
  :prefix "casl-indent-")

(defcustom casl-indent-offset 5
  "*Indentation of casl statements with respect to containing block."
  :type 'integer
  :group 'casl-indent)

(defcustom casl-indent-rhs-align-column 0 
  "*Column on which to align right-hand sides (use 0 for ad-hoc alignment)." 
  :type 'integer 
  :group 'casl-indent) 

(defsubst casl-indent-get-beg-of-line (&optional arg)
  (save-excursion
    (beginning-of-line arg)
    (point)))

(defsubst casl-indent-get-end-of-line (&optional arg)
  (save-excursion
    (end-of-line arg)
    (point)))

(defun casl-indent-point-to-col (apoint)
  "Returns the column number of APOINT."
  (save-excursion
    (goto-char apoint)
    (current-column)))

(defconst casl-indent-start-keywords-re 
  (concat "\\<\\("
	  "spec\\|then\\|view\\|units"
	  "\\)\\>")
  "Regexp describing keywords to complete when standing at the first word
of a line.")

(defconst casl-indent-dont-indent-re
  "\\(\\<library\\|\\<version\\|\\(%\\(authors\\|date\\|display\\):?\\)\\)"
  "These keywords need not to be indented.")

(defconst casl-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "t when using XEmacs or Lucid.")

;;; customizations for different kinds of environments
;;; in which dealing with low-level events are different
(if casl-running-xemacs
    (progn ;;; for XEmacs
      (fset 'event-basic-type 'event-key)
      (fset 'read-event 'next-command-event)
      (defun casl-indent-mark-active ()
	(if zmacs-regions
	    zmacs-region-active-p
	  t)))
  ;; in Gnu  Emacs
  (defun casl-indent-mark-active ()
    mark-active)
  )

;;  for pushing indentation information

(defun casl-indent-push-col (col &optional name)
  "Pushes indentation information for the column COL
followed by NAME (if present). Makes sure that the same indentation info
is not pushed twice in a row. Uses free var `indent-info'."
  (let ((tmp (cons col name)))
       (if (and indent-info (equal tmp (car indent-info)))
           indent-info
         (push tmp  indent-info))))

(defun casl-indent-push-pos (pos &optional name)
  "Pushes indentation information for the column corresponding to POS
followed by NAME (if present). "
  (casl-indent-push-col (casl-indent-point-to-col pos) name))

(defun casl-indent-push-pos-offset (pos &optional offset)
  "Pushes indentation information for the column corresponding to POS
followed by an OFFSET (if present use its value otherwise use
`casl-indent-offset')."
  (casl-indent-push-col (+ (casl-indent-point-to-col pos)
                              (or offset casl-indent-offset))))

;;; redefinition of some Emacs function for dealing with
;;; Bird Style literate scripts 

(defun casl-indent-bolp ()
  "`bolp'"
  (bolp)
  )

(defun casl-indent-empty-line-p ()
  "Checks if the current line is empty."
  (save-excursion
    (beginning-of-line)
    (looking-at "[ \t]*$"))
  )

(defun casl-indent-back-to-indentation ()
  "`back-to-indentation' function."
  (back-to-indentation)
  )

(defun casl-indent-current-indentation ()
  "`current-indentation' function."
  (current-indentation)
  )

(defun casl-indent-backward-to-indentation (n)
  "`backward-to-indentation' function."
  (backward-to-indentation n)
  )

(defun casl-indent-forward-line (&optional n)
  "`forward-line' function."
  (forward-line n)
  )

(defun casl-indent-line-to (n)
  "`indent-line-to' function."
  (indent-line-to n)
  )

(defun casl-indent-skip-blanks-and-newlines-forward (end)
  "Skips forward blanks, tabs and newlines until END."
  (skip-chars-forward " \t\n" end)
)

(defun casl-indent-skip-blanks-and-newlines-backward (start)
  "Skips backward blanks, tabs and newlines upto START."
  (skip-chars-backward " \t\n" start)
)

;;; Start of indentation code

(defun casl-indent-start-of-def ()
  "Returns the position of the start of a definition.
It is at the first character which is not in a comment after nearest
preceding non-empty line."
  (save-excursion
    (let (start-code
          (save-point (point)))
      ;; determine the starting point of the current piece of code
      (setq start-code 1)
      ;; go backward until the first preceding empty line
      (casl-indent-forward-line -1)
      (while (and (not (casl-indent-empty-line-p))
                  (> (point) start-code)
                  (= 0 (casl-indent-forward-line -1))))
      ;; go forward after the empty line
      (if (casl-indent-empty-line-p)
          (casl-indent-forward-line 1))
      ;; find the first line of code which is not a comment
      (while (and (casl-indent-in-comment start-code (point))
                  (= 0 (casl-indent-forward-line 1))))
      (casl-indent-skip-blanks-and-newlines-forward save-point)
      (point)))
  )

(defun casl-indent-open-structure (start end)
  "If any structure (list or tuple) is not closed, between START and END,
returns the location of the opening symbol, nil otherwise."
  (save-excursion
    (let ((pps (parse-partial-sexp start end)))
      (if (> (nth 0 pps) 0)
          (nth 1 pps))
      )))

(defun casl-indent-in-comment (start end)
  "Checks, starting from START, if END is within a comment, returns
the location of the start of the comment, nil otherwise."
  (cond ((> start end) end)
        ((= start end) nil)
        ( t
          (save-excursion
            (cond
             ((looking-at "%{\\|%%\\|%\\[\\|%\(")   ; on the first char of a comment ?
              (point))
             ((and (= (preceding-char) ?%) ; on the second char ?
                   (or (= (following-char) ?\%)
		       (= (following-char) ?\[)
		       (= (following-char) ?\()
                       (= (following-char) ?\{)))
              (1- (point)))
             (t (let ((pps (parse-partial-sexp start end)))
                  (if (nth 4 pps)
                      (progn (re-search-backward "%{" (nth 2 pps) t)
			     (re-search-backward "%\\[" (nth 2 pps) t)
			     (re-search-backward "%\(" (nth 2 pps) t))
                    (re-search-backward "%%"
                                        (casl-indent-get-beg-of-line) t))))
             ))))
  )

;; Keine Ahnung
(defvar casl-indent-off-side-keywords-re
      "\\<\\(with\\|to\\|and\\|hide\\)\\>[ \t]*")

(defun casl-indent-type-at-point ()
  "Returns the type of the line (also puts information in `match-data')."
  (cond
   ((casl-indent-empty-line-p) 'empty)
   ((casl-indent-in-comment 1 (point)) 'comment)
   ;; [_.] fuer __>__ Form und ., die Zeile die mit 'from', 'library', 
   ;; 'logic' sowie '%xxxx' anfaengt, wird auch als ein indent angewendet.
   ((looking-at (concat "\\("
                        "\\([a-zA-Z_.%]\\S-*\\)"
                        "[ \t\n]*\\)")) 'ident)
   ;; fuer type-definition
   ((looking-at "\\(|[^|_]\\)[ \t\n]*") 'guard)
   ;; rhs ist in CASL nicht wichtig
   ((looking-at  "\\(::=[^>=]\\)[ \t\n]*") 'rhs)
   ; ((looking-at "\\(%\\sw+\\)") 'muell)
   ( t 'other))
  )

(defvar casl-indent-current-line-first-ident ""
  "Global variable that keeps track of the first ident of the line to indent.")

(defun casl-indent-contour-line (start end)
  "Generates contour information between START and END points."
  (if (< start end)
      (save-excursion
        (let ((cur-col 1024)            ; maximum column number
              (fl 0)     ; number of lines that forward-line could not advance
              contour)
          (goto-char end)
          (casl-indent-skip-blanks-and-newlines-backward start)
          (while (and (> cur-col 0) (= fl 0) (>= (point) start))
            (casl-indent-back-to-indentation)
            (and (not (member (casl-indent-type-at-point)
                              '(empty comment))) ; skip empty and comment lines
                 (< (current-column) cur-col) ; less indented column found
                 (push (point) contour) ; new contour point found
                 (setq cur-col (current-column)))
            (setq fl (casl-indent-forward-line -1))
            )
          contour))))

(defun casl-indent-next-symbol (end)
  "Puts point to the next following symbol."
  (while (and (looking-at "\\s)")       ;skip closing parentheses
              (< (point) end))
    (forward-char 1))
  (if (< (point) end)
     (progn
       (forward-sexp 1)  ; this skips also %{ comments !!! -- funktioniert??
       (casl-indent-skip-blanks-and-newlines-forward end))
    ))

(defun casl-indent-separate-valdef (start end)
  "Returns a list of positions for important parts of a valdef."
  (save-excursion
    (let (valname valname-string aft-valname
                  rhs-sign aft-rhs-sign 
		  guard aft-guard
                  type)
      ;; "parse" a valdef separating important parts
      (goto-char start)
      (setq type (casl-indent-type-at-point))
      (if (or (eq type 'ident) (eq type 'other)) ; possible start of a value def
          (progn
            (if (eq type 'ident)
                (progn
                  (setq valname (match-beginning 0))
                  (setq valname-string (buffer-substring (match-beginning 0)
                                                         (match-end 0)))
                  (goto-char (match-end 0)))
              (skip-chars-forward " \t" end)
              (setq valname (point))    ; type = other
              (casl-indent-next-symbol end))
            (while (and (< (point) end)
                        (setq type (casl-indent-type-at-point))
                        (or (eq type 'ident) (eq type 'other)))
              (if (null aft-valname)
                  (setq aft-valname (point)))
              (casl-indent-next-symbol end))))
      (if (and (< (point) end) (eq type 'rhs)) ; start of a rhs
          (progn
            (setq rhs-sign (match-beginning 0))
            (goto-char (match-end 0))
            (while (and (< (point) end)
                        (setq type (casl-indent-type-at-point))
                        (not (eq type 'guard)))
              (if (null aft-rhs-sign)
                  (setq aft-rhs-sign (point)))
              (casl-indent-next-symbol end))))
      (if (and (< (point) end) (eq type 'guard)) ; start of a guard
          (progn
            (setq guard (match-beginning 0))
            (goto-char (match-end 0))
           (if (< (point) end)
                (setq aft-guard (point)))))
      (list valname valname-string aft-valname
	    rhs-sign aft-rhs-sign
	    guard aft-guard))))    

(defun casl-indent-guard (start end end-visible indent-info)
  "Finds indentation information for a line starting with a guard."
  (save-excursion
    (let* ((sep (casl-indent-separate-valdef start end))
           (valname (nth 0 sep))
           (rhs-sign (nth 3 sep))
	   (guard (nth 5 sep)))
      ;; push information indentation for the visible part
      (if (and guard (< guard end-visible))
          (casl-indent-push-pos guard)
	(if rhs-sign
	    (casl-indent-push-pos-offset rhs-sign 2) ; behind "::="
	  (if valname
	      (casl-indent-push-pos-offset valname)
	    )))))
  indent-info)

(defun casl-indent-rhs (start end end-visible indent-info)
  "Finds indentation information for a line starting with a rhs."
  (save-excursion
    (let* ((sep (casl-indent-separate-valdef start end))
           (valname (nth 0 sep))
           (rhs-sign (nth 3 sep))
	   (guard (nth 5 sep)))
      ;; push information indentation for the visible part
      (if (and rhs-sign (< rhs-sign end-visible))
	  (casl-indent-push-pos rhs-sign)
	(if (and guard (< guard end-visible))
	    (casl-indent-push-pos-offset guard)
	  (if valname
	      (casl-indent-push-pos-offset valname)
	    (casl-indent-push-pos-offset valname))))))
  indent-info)

(defun casl-indent-comment (start end indent-info)
  "Finds indentation information for a comment line.
If the previous line (between START and END) is also a comment line
   -- comments are aligned on their start
   {- comments are aligned on the first non-blank char following the open {
otherwise
    indent at the same indentation as the previous line."
  (save-excursion
    (let ((comment-start (casl-indent-in-comment start end)))
      (if comment-start
          (if (eq (following-char comment-start) ?%)
              ;; %% style comment
              (casl-indent-push-pos comment-start) 
            ;;  %{ style comment
            (goto-char (+ 2 comment-start))
            (casl-indent-skip-blanks-and-newlines-forward end)
            (casl-indent-push-pos (point)))
        ;; no previous comment indent with previous line
        (casl-indent-push-col (casl-indent-current-indentation)))))
    indent-info)   

(defconst casl-indent-decision-table
  (let ((or "\\)\\|\\("))
    (concat "\\("
	    "111111"     or               ;1 = vn avn rh arh gd agd
	    "1.0000"     or               ;2 = vn avn
	    "1.1000"     or               ;3 = vn (avn) rh
	    "111100"     or               ;4 = vn avn rh arh
	    "000011"     or               ;5 = gd agd
	    "001000"     or               ;6 = rh
	    "0011.."     or               ;7 = rh arh . .
	    "101..."     or               ;8 = vn rh (arh gd agd)
            "000000"                      ;9 = 
            "\\)")))         

(defun casl-indent-find-case (test)
  "Find the index that matches in the decision table."
  (if (string-match casl-indent-decision-table test)
      ;; use the fact that the resulting match-data is a list of the form
      ;; (0 6 [2*(n-1) nil] 0 6) where n is the number of the matching regexp
      ;; so n= ((length match-date)/2)-1
      (- (/ (length (match-data)) 2) 1)
    (error "casl-indent-find-case: impossible case: %s" test)
    ))

(defun casl-indent-empty (start end end-visible indent-info)
  "Finds indentation points for an empty line."
  (save-excursion
    (let*
        ((sep (casl-indent-separate-valdef start end))
         (valname (pop sep))
         (valname-string (pop sep))
         (aft-valname (pop sep))
         (rhs-sign (pop sep))
         (aft-rhs-sign (pop sep))
         (guard (pop sep))
         (aft-guard (pop sep))
         (last-line (= end end-visible))
         (test (concat
                (if valname "1" "0")
                (if (and aft-valname (< aft-valname end-visible)) "1" "0")
                (if (and rhs-sign (< rhs-sign end-visible)) "1" "0")
                (if (and aft-rhs-sign (< aft-rhs-sign end-visible)) "1" "0")
                (if (and guard (< guard end-visible)) "1" "0")
                (if (and aft-guard (< aft-guard end-visible)) "1" "0")))
         )
      (message "face: %s" test)
      (if (and valname-string           ; special case for start keywords
               (string-match casl-indent-start-keywords-re valname-string))
          (progn
            (casl-indent-push-pos valname)
	    (casl-indent-push-pos-offset valname)
	    )
	(if (and valname-string
		 (string-match casl-indent-dont-indent-re valname-string))
		 (casl-indent-push-pos valname)
	  (case                           ; general case
	   (casl-indent-find-case test)
	   ;; "111111"   1 = all elements
	   (1 (casl-indent-push-pos valname)
	      (casl-indent-push-pos-offset rhs-sign 2)
	      (casl-indent-push-pos guard))
	   ;; "1.0000"   2= vn avn
	   (2 (casl-indent-push-pos valname)
	      (if aft-valname
		  (casl-indent-push-pos aft-valname)
		(casl-indent-push-pos valname valname-string)))
	   ;; "1.1000"   3= vn (avn) rh
	   (3 (casl-indent-push-pos valname)
	      (if aft-valname 
		  (casl-indent-push-pos aft-valname))
	      (casl-indent-push-pos-offset rhs-sign 2)
	      )
	   ;; "111100"   4= vn avn rh arh
	   (4 (casl-indent-push-pos valname)
	      (casl-indent-push-pos-offset rhs-sign 2))
	   ;; "000011"   5= gd agd 
	   (5 (casl-indent-push-pos guard))
	   ;; "001000"   6= rh 
	   (6 (casl-indent-push-pos rhs-sign))
	   ;; "0011.."   7= rh arh (gd agd)
	   (7 (casl-indent-push-pos-offset rhs-sign 2))
	   ;; "101..."   8 = vn rh (arh gd agd)
	   (8 (if guard (casl-indent-push-pos guard))
	      (casl-indent-push-pos valname))
	   ;; "000000"   9= 
	   (t (error "casl-indent-empty: %s impossible case" test )
	      ))))))
    indent-info)

(defun casl-indent-ident (start end end-visible indent-info)
  "Finds indentation points for a line starting with an identifier."
  (save-excursion
    (let*
        ((sep (casl-indent-separate-valdef start end))
         (valname (pop sep))
         (valname-string (pop sep))
         (aft-valname (pop sep))
         (rhs-sign (pop sep))
         (aft-rhs-sign (pop sep))
         (guard (pop sep))
         (aft-guard (pop sep))
         (last-line (= end end-visible))
         (test (concat
                (if valname "1" "0")
                (if (and aft-valname (< aft-valname end-visible)) "1" "0")
                (if (and rhs-sign (< rhs-sign end-visible)) "1" "0")
                (if (and aft-rhs-sign (< aft-rhs-sign end-visible)) "1" "0")
                (if (and guard (< guard end-visible)) "1" "0")
                (if (and aft-guard (< aft-guard end-visible)) "1" "0")))
	 )
      (if (and valname-string           ; special case for start keywords
               (string-match casl-indent-start-keywords-re valname-string))
          (progn
            (casl-indent-push-pos valname)
            (if (not (string-match
                        casl-indent-start-keywords-re
                        casl-indent-current-line-first-ident))
                  (casl-indent-push-pos-offset valname))
              )
	(if (and valname-string
		 (string-match casl-indent-dont-indent-re valname-string))
	    (casl-indent-push-pos valname)
	  (case                         ; general case
	   (casl-indent-find-case test)
	   ;; "111111"   1 = all elements
	   (1 (casl-indent-push-pos valname))
	   ;; "1.0000"   2= vn avn
	   (2 (casl-indent-push-pos valname)
	      (if aft-valname
		  (casl-indent-push-pos aft-valname)
		(casl-indent-push-pos valname valname-string)))
	   ;; "1.1000"   3= vn (avn) rh
	   (3 (casl-indent-push-pos-offset rhs-sign 2))
	   ;; "111100"   4= vn avn rh arh
	   (4 (casl-indent-push-pos valname))
	   ;; "000011"   5= gd agd 
	   (5 ;; (casl-indent-push-pos 0)
	    (casl-indent-push-pos guard))
	   ;; "001000"   6= rh 
	   (6 (casl-indent-push-pos rhs-sign))
	   ;; "0011.."   7= rh arh (gd agd)
	   (7 
	    (casl-indent-push-pos-offset rhs-sign 2))
	   ;; "101..."   8 = vn rh (arh)
	   (8 (casl-indent-push-pos valname))
	   ;; "000000"  9= 
	   (t (error "casl-indent-ident: %s impossible case" test )))))))
    indent-info)

(defun casl-indent-other (start end end-visible indent-info)
  "Finds indentation points for a non-empty line starting with something other
than an identifier, a guard or rhs."
  (save-excursion
    (let*
        ((sep (casl-indent-separate-valdef start end))
         (valname (pop sep))
         (valname-string (pop sep))
         (aft-valname (pop sep))
         (rhs-sign (pop sep))
         (aft-rhs-sign (pop sep))
         (guard (pop sep))
         (aft-guard (pop sep))
         (last-line (= end end-visible))
         ;(is-where
         ; (string-match "where[ \t]*" casl-indent-current-line-first-ident))
         (test (concat
                (if valname "1" "0")
                (if (and aft-valname (< aft-valname end-visible)) "1" "0")
                (if (and rhs-sign (< rhs-sign end-visible)) "1" "0")
                (if (and aft-rhs-sign (< aft-rhs-sign end-visible)) "1" "0")
                (if (and guard (< guard end-visible)) "1" "0")
                (if (and aft-guard (< aft-guard end-visible)) "1" "0")))
         )
      (if (and valname-string           ; special case for start keywords
               (string-match casl-indent-start-keywords-re valname-string))
          (casl-indent-push-pos-offset valname)
        (case                           ; general case
         (casl-indent-find-case test)
	 ;; "111111"   1 = all elements
	 (1 (casl-indent-push-pos valname))
	 ;; "1.0000"   2= vn avn
	 (2 (casl-indent-push-pos-offset valname))
	 ;; "1.1000"   3= vn (avn) rh
	 (3 (casl-indent-push-pos valname))
	 ;; "111100"   4= vn avn rh arh
	 (4 (casl-indent-push-pos valname))
	 ;; "000011"   5= gd agd 
	 (5 (casl-indent-push-pos guard))
	 ;; "001000"   6= rh 
	 (6 (casl-indent-push-pos-offset rhs-sign 2))
	 ;; "0011.."   7= rh arh (gd agd)
	 (7 ())
	 ;; "101.00"   8 = vn rh (arh)
	 (8 (casl-indent-push-pos valname))
         ;; "000000"   9= 
         (t (error "casl-indent-other: %s impossible case" test ))))))
  indent-info)

(defun casl-indent-valdef-indentation (start end end-visible curr-line-type
                                      indent-info)
  "Finds indentation information for a value definition."
  (if (< start end-visible)
      (case curr-line-type
            ('empty (casl-indent-empty start end end-visible indent-info))
            ('ident (casl-indent-ident start end end-visible indent-info))
            ('guard (casl-indent-guard start end end-visible indent-info))
            ('rhs   (casl-indent-rhs start end end-visible indent-info))
            ('comment (error "Comment indent should never happen"))
            ('other (casl-indent-other start end end-visible indent-info)))
    indent-info))

(defun casl-indent-line-indentation (line-start line-end end-visible
                                         curr-line-type indent-info)
  "Separate a line of program into valdefs between offside keywords
and find indentation info for each part."
  (save-excursion
    (let (end-match beg-match start-comment)
      ;; point is (already) at line-start
      (setq start-comment (casl-indent-in-comment line-start line-end))
      (if start-comment                         ; if comment at the end
          (setq line-end (- start-comment 1)))  ; end line before it
      ;; loop on all parts separated by off-side-keywords
      (while (re-search-forward casl-indent-off-side-keywords-re line-end t)
        (setq beg-match (match-beginning 0)); save beginning of match
        (setq end-match (match-end 0))  ; save end of match
        (if (casl-indent-in-comment line-start (point)) ; keyword in a {- comment
            (progn
              (setq indent-info
                    (casl-indent-valdef-indentation
                     line-start ; end line before comment
                     (- (search-backward "%\{" line-start) 1)
                     end-visible curr-line-type indent-info))
                                        ;skip past end of comment
              (re-search-forward "\}%[ \t]*" line-end 'move) 
              (setq line-start (point)))
          ;; not in a comment    
          (if (< line-start beg-match) ; if off-side-keyword at the start
                (setq indent-info       ; do not try to find indentation points
                  (casl-indent-valdef-indentation line-start beg-match
                                           end-visible
                                           curr-line-type indent-info))
            ;; but keep the start of the line if keyword alone on the line 
            (if (= line-end end-match)
                (casl-indent-push-pos beg-match)))
	  (setq line-start end-match)
	  (goto-char line-start)))
      (setq indent-info
            (casl-indent-valdef-indentation line-start line-end end-visible
					    curr-line-type indent-info))))
  indent-info)

(defun casl-indent-indentation-info ()
  "Returns a list of possible indentations for the current line that 
are then used by `casl-indent-cycle'."
  (let ((start (casl-indent-start-of-def))
        (end (progn (casl-indent-back-to-indentation) (point)))
        indent-info open follow contour-line pt)
    ;; open structure? ie  ( { [  
    (if (setq open (casl-indent-open-structure start end))
	;; there is an open structure to complete
	(if (looking-at "\\s)\\|\\s.\\|$ ")
	    (casl-indent-push-pos open); align a ) or punct with (
	  (progn      
	    (setq follow (save-excursion
			   (goto-char (1+ open))
			   (casl-indent-skip-blanks-and-newlines-forward end)
			   (point)))
	    (if (= follow end)
		(casl-indent-push-pos-offset open 1)
	      (casl-indent-push-pos follow))))
      ;; in comment ?
      (if (casl-indent-in-comment start end)
	  (save-excursion
	    (end-of-line 0)  ; put point at the end of preceding line before
	    (setq indent-info         ; computing comment indentation
		  (casl-indent-comment (casl-indent-get-beg-of-line)
				       (point) indent-info)))
	;; full indentation
	(setq contour-line (casl-indent-contour-line start end))
	(if contour-line
	    (let* ((curr-line-type (casl-indent-type-at-point))
		   line-start line-end end-visible)
	      (save-excursion
		(if (eq curr-line-type 'ident)
		    (progn            ; guess the type of line
		      (setq sep
			    (casl-indent-separate-valdef (point)
							 (casl-indent-get-end-of-line)))
		      ;; if the first ident is where or the start of a def
		      ;; keep it in a global variable
		      (if (nth 3 sep) ; is there a rhs-sign
			  (setq casl-indent-current-line-first-ident
				(nth 1 sep))
			(setq casl-indent-current-line-first-ident ""))))
		(while contour-line   ; explore the contour points
		  (setq line-start (pop contour-line))
		  (goto-char line-start)
		  (setq line-end (casl-indent-get-end-of-line))
		  (setq end-visible   ; visible until the column of the
			(if contour-line ; next contour point 
			    (save-excursion 
			      (move-to-column
			       (casl-indent-point-to-col (car contour-line)))
			      (point))
			  line-end))
		  (if (and (not (casl-indent-open-structure start line-start))
			   (not (casl-indent-in-comment start line-start)))
		      (setq indent-info
			    (casl-indent-line-indentation line-start line-end
							  end-visible curr-line-type
							  indent-info)))
		  )))
	  ;; simple contour just one indentation at start
	  (casl-indent-push-pos start)))
      indent-info
      )))

(defun casl-indent-event-type (event)
  "Checks if EVENT is the TAB or RET key before returning the value
of `event-basic-type'. Needed for dealing with the case that Emacs
is not in a windowing environment."
  (cond ((eq event ?\t) 'tab)
        ((eq event ?\r) 'return)
        (t (event-basic-type event)))
  )
  
(defun casl-indent-cycle ()
  "Indentation cycle.
We stay in the cycle as long as the TAB key is pressed.
Any other key or mouse click terminates the cycle and is interpreted 
with the exception of the RET key which merely exits the cycle."
  (interactive "*")
    (let (il indent-list com indent-info cdrii marker)
      (if (> (current-column) (casl-indent-current-indentation))
          (setq marker (point-marker)))
      (setq il (setq indent-list (casl-indent-indentation-info)))
      ;;(message "Indent-list:%s" indent-list) (read-event) ; uncomment for debug!!
      (setq indent-info (car il))
      (casl-indent-line-to (car indent-info)) ; insert indentation
      (if (= (length indent-list) 1)
          (message "Sole indentation")
        (message (format "Indent cycle (%d)..." (length indent-list)))
        (while (equal (casl-indent-event-type (setq com (read-event))) 'tab)
          (setq il (cdr il))            ; get next insertion
          (or il (setq il indent-list)) ; if at the end of insertion, restart
                                        ; from the beginning
          (setq indent-info (car il))
          (casl-indent-line-to (car indent-info)) ; insert indentation
          (message "Indenting..."))
        (if (not (equal (casl-indent-event-type com) 'return))
            (setq unread-command-events (list com)))
        (message "Done."))
      (if marker
          (goto-char (marker-position marker)))
      )
  )
;;; alignment functions
;;;
(defun casl-indent-shift-columns (dest-column region-stack)
  "Shifts columns in region-stack to go to DEST-COLUMN.
Elements of the stack are pairs of points giving the start and end
of the regions to move."
  (let (reg col diffcol reg-end)
    (while (setq reg (pop region-stack))
      (setq reg-end (copy-marker (cdr reg)))
      (goto-char (car reg))
      (setq col (current-column))
      (setq diffcol (- dest-column col))
      (if (not (zerop diffcol))
          (catch 'end-of-buffer
            (while (<= (point) (marker-position reg-end))
              (if (< diffcol 0)
                  (backward-delete-char-untabify (- diffcol) nil)
                (insert-char ?\  diffcol))
              (end-of-line 2)           ; should be (forward-line 1)
              (if (eobp)                ; but it adds line at the end...
                  (throw 'end-of-buffer nil))
              (move-to-column col)))
        ))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; turn-on-casl-indent to be used in conjunction with
;;; the casl-mode of Graeme E Moss and Tommy Thorn
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun turn-on-casl-indent ()
  "Turn on ``intelligent'' casl indentation mode."
  (interactive)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'casl-indent-cycle)
  (local-set-key "\t"    'casl-indent-cycle)
  (setq casl-indent-mode t)
  (run-hooks 'casl-indent-hook)
  )

(defun turn-off-casl-indent ()
  "Turn off ``intelligent'' casl indentation mode that deals with
the layout rule of casl."
  (interactive)
  (setq indent-line-function 'indent-to-left-margin)
  (local-unset-key "\t")
  (setq casl-indent-mode nil)
  )

(defvar casl-indent-mode nil
  "Indicates if the semi-intelligent casl indentation mode is in effect
in the current buffer.")
(make-variable-buffer-local 'casl-indent-mode)

;; Put this minor mode on the global minor-mode-alist.
(or (assq 'casl-indent-mode (default-value 'minor-mode-alist))
    (setq-default minor-mode-alist
                  (append (default-value 'minor-mode-alist)
                          '((casl-indent-mode " Ind")))))

(defun casl-indent-mode (&optional arg)
  "``intelligent'' casl indentation mode that deals with
the layout rule of casl.  
Invokes `casl-indent-hook' if not nil."
  (interactive "P")
  (setq casl-indent-mode
        (if (null arg) (not casl-indent-mode)
          (> (prefix-numeric-value arg) 0)))
  (if casl-indent-mode
      (turn-on-casl-indent)
    (turn-off-casl-indent)))

(provide 'casl-indent)

;; EOF