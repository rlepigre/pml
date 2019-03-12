;;; This is pml2 emacs mode
(provide 'pml2-mode)

;;; SYNTAX TABLE
;;; defining the type of characters
(defvar pml2-mode-syntax-table
  (let ((pml2-mode-syntax-table (make-syntax-table)))

    ;; This is added so entity names with underscores can be more easily parsed
    (modify-syntax-entry ?_ "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?' "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?( "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?{ "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?[ "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?) ")" pml2-mode-syntax-table)
    (modify-syntax-entry ?} ")" pml2-mode-syntax-table)
    (modify-syntax-entry ?] ")" pml2-mode-syntax-table)
    ;; comments definition
    ;; . means punctuation
    ;; // 12 means first and second char of one line comments
    ;; The second space charater is ignored
    (modify-syntax-entry ?/ ". 12" pml2-mode-syntax-table)
    ;; newlines end comments
    (modify-syntax-entry ?\n ">" pml2-mode-syntax-table)
    pml2-mode-syntax-table)
  "Syntax table for pml2-mode")

(defconst pml2-font-lock-keywords
  (list (cons (concat "\\<"
		      (regexp-opt
                       '("assert" "assume" "because" "bool" "by" "case" "check"
                        "corec" "deduce" "def" "delim" "else" "eqns" "false"
                        "fix" "for" "fun" "if" "infix" "include" "know" "let"
                        "of" "print" "qed" "rec" "restore" "save" "set"
                        "show" "showing" "sort" "such" "suppose" "take"
                        "that" "true" "type" "use" "using" "val"))
                      "\\>")
              'font-lock-keyword-face)
        (cons (concat "\\<"
		      (regexp-opt
		      '("unsafe"))
                      "\\>")
              'font-lock-warning-face)
        )
  "Minimal highlighting expressions for pml2 mode.")

;;; QUAIL to be able to input unicode
(require 'quail)
(quail-define-package
 "Pml2" "Pml2" "x⃗" t
 "A transliteration scheme for Pml2."
 nil t t t t nil t nil nil nil t)
(quail-define-rules
 ("..." ?⋯)     ("\\dots" ?⋯)
 ("->" ?→)      ("\\to" ?→)
 ("=>" ?⇒)      ("\\To" ?⇒)
 ("~>" ?↝)
 ("8<" ?✂)      ("\\scicors" ?✂)
 ("==" ?≡)      ("\\equiv" ?≡)
 ("!=" ?≠)      ("\\notequiv" ?≠)
                ("\\not" ?¬)
 ("\\*" ?×)     ("\\times" ?×)
 ("\\l" ?λ)     ("\\lambda" ?λ)
 ("\\i" ?ι)     ("\\iota" ?ι)
 ("\\t" ?τ)     ("\\tau" ?τ)
 ("\\s" ?σ)     ("\\sigma" ?σ)
 ("\\o" ?ο)     ("\\omicron" ?ο)
 ("\\k" ?κ)     ("\\kappa" ?κ)
 ("|->" ?↦)     ("\\mapsto" ?↦)
 ("\\<" ?⟨)     ("\\langle" ?⟨)
 ("\\>" ?⟩)     ("\\rangle" ?⟩)
 ("<=" ?≤)      (">=" ?≥)
 ("\\A" ?∀)     ("\\forall" ?∀)
 ("\\E" ?∃)     ("\\exists" ?∃)
                ("\\in" ?∈)
 ("\\e"  ?ε)    ("\\epsilon" ?ε)
 ("\\m" ?μ)     ("\\mu" ?μ)
 ("\\n" ?ν)     ("\\nu" ?ν)
 ("\\8" ?∞)     ("\\infty" ?∞)
;; ("\\v" ?↓)     ("\\downarrow" ?↓)
;; ("\\ni" ?∉)    ("\\notin" ?∉)
;; ("\\<" ?⊂)     ("\\subset" ?⊂)
 )

;; USEFUL FUNCTION FOR INLINING
;; Relies on syntax tables!
;; test for closing char at current pos
(defun pml2-is-closing ()
  (or (equal (char-after) ?\))
      (equal (char-after) ?\])
      (equal (char-after) ?})))

;; parenthesis depth, need a fix when at closing
(defun pml2-depth (&optional pos)
  (if pos (goto-char pos))
  (let ((depth (car (syntax-ppss))))
    (if (pml2-is-closing)
        (- depth 1) depth)))

;; search of regular expression at the same depth level
(defun pml2-search-backward-regex-same-lvl (regex &optional depth)
  (save-excursion
    (let
        ((depth (if depth depth (pml2-depth)))
         (depth2 nil)
         (limit (car (cdr (syntax-ppss))))
         (found nil))
      (while (or (not depth2) (> depth2 depth))
        (setq found (search-backward-regexp regex limit t))
        (setq depth2 (if found (pml2-depth) -1)))
      (if found (match-beginning 0) nil))))

(defun pml2-search-forward-regex-same-lvl (regex &optional depth)
  (save-excursion
    (let
        ((depth (if depth depth (pml2-depth)))
         (depth2 nil)
         (limit (progn (save-excursion (end-of-line) (point))))
         (found nil))
      (while (or (not depth2) (> depth2 depth))
        (setq found (search-forward-regexp regex limit t))
        (setq depth2 (if found (pml2-depth) -1)))
      (if found (match-beginning 0) nil))))

;; toplevel symbols
(defvar pml2-top-regex
  "\\(def\\)\\|\\(include\\)\\|\\(type\\)\\|\\(val\\)\\|\\(assert\\)\\|\\(sort\\)")
(defun pml2-top (&optional pos)
  (save-excursion
    (if pos (goto-char pos))
    (looking-at pml2-top-regex)))

;; move to the first non blank char at the beginning of a
;; line. Return nil if the line has only blank
(defun pml2-move-to-first-non-blank (&optional ignored)
  (end-of-line)
  (let ((pos (point)) (res nil))
    (beginning-of-line)
    (while (and (setq res (search-forward-regexp "[^ \t\n\r]" pos t))
                ignored
                (memq (char-before) ignored)))
    (if res (progn (backward-char) t) nil)))

;; test if a line is entirely a comment
(defun pml2-is-comment-line ()
  (save-excursion
    (pml2-move-to-first-non-blank)
    (looking-at "//")))

;; line forward and backward
(defun pml2-move-to-previous-non-empty-line (&optional comments)
  (forward-line -1)
  (while (and (> (line-number-at-pos) 1)
              (or (not (pml2-move-to-first-non-blank))
                  (and (not comments) (pml2-is-comment-line))))
    (forward-line -1)))

(defun pml2-move-to-next-non-empty-line ()
  (forward-line 1)
  (while (and (> (line-number-at-pos) 1) (not (pml2-move-to-first-non-blank)))
    (forward-line 1)))

;; INLINIG CODE
;; We distinguish three categories of lines
;; case line: have an arrow at the same depth as the beginning of the line
;; init line: the previous line ends with a semi columns
;; def  line: line with an "=" and ":" and no semi column
;;            or arrow after at the same depth

(defvar pml2-case-regex "\\(\\(→\\)\\|\\(->\\)\\)")
(defvar pml2-semi-regex "\\(;[ \t]*$\\)")
(defvar pml2-def-regex  "[:=]")
(defvar pml2-case-or-semi-regex (concat pml2-case-regex "\\|" pml2-semi-regex))
(defvar pml2-any-ref-regex (concat pml2-case-or-semi-regex "\\|" pml2-def-regex))
(defvar pml2-start-def-regex "\\(var\\)\\|\\(let\\)\\|\\(type\\)\\|\\(def\\)")

(defvar pml2-non-blank "[ \t]*[^ \t\n\r]") ; only used with looking-at

;; test if line is a case line
(defun pml2-is-case (&optional depth)
  (if (pml2-search-forward-regex-same-lvl pml2-case-regex depth) t nil))

;; test if a line is a semi line
(defun pml2-after-semi ()
  (save-excursion
    (pml2-move-to-previous-non-empty-line)
    (let ((limit (point)))
      (end-of-line)
      (search-backward-regexp pml2-semi-regex limit t))))

;; move backward to the delimiter of the current depth
;; or the first non blank char, on the same line
(defun pml2-move-to-delim-or-first ()
  (let ((delim (car (cdr (syntax-ppss)))))
    (pml2-move-to-first-non-blank)
    (if (and delim (> delim (point)))
        (progn (goto-char delim)
               (if (looking-at  pml2-non-blank)
                   (forward-char 2)
                 (pml2-move-to-first-non-blank '(?\; ?|)))))))

;; debugging function for incentation
(defvar pml2-debug-indent nil)

(defun pml2-dbg (&rest args)
  (if pml2-debug-indent (print args)))

;; The three next function are the heart of our indenting algo
;; depending of the nature of the current line (case, semi or other),
;; we search for a previous line, at the same depth, that matches:
;; - only case line matches case line
;; - case and semi line match semi line
;; - any thee kind of lines matches the other lines (at the same depth still!)
;; If no line matches, we find the first line at a lower depth

;; we have find a matching lines, the parameter indicates
;; the nature of the original line. We know the
;; nature of the matching line using (match-string 0)
;; this function return a pair (b . n)
;; - n is the reference position for indenting
;; - b = t, means indent at the position
;; - b = nil, means atra indent propotionnally to the depth difference
(defun pml2-move-if-found (is-case is-semi)
  (goto-char (match-end 0))
  (pml2-dbg "pml2-move-if-found" (point) is-case is-semi)
  ;; the matching line is a semi line
  (cons t
    (if (equal (substring (match-string 0) 0 1) ";")
        (progn ;; we are on the previous line !
          (pml2-dbg "semi")
          (pml2-move-to-next-non-empty-line)
          (pml2-move-to-delim-or-first)
          ;; extra indent if the current line is not a semi line
          (if (not is-semi) (+ (current-column) 2)
            (current-column)))
      ;; the matching line is a case line
      (if (or (equal (match-string 0) "->")
              (equal (match-string 0) "→"))
          ;; position after the arrow if there is something on the line
          (progn
            (pml2-dbg "case" )
            (if (and (not is-case) (looking-at pml2-non-blank))
                (+ (current-column) 1)
              (pml2-move-to-delim-or-first)
              ;; extra indent if the original line is not a case line
              (if (not is-case) (+ (current-column) 2)
                (current-column))))
        ;; for def line, if we found = or :
        (pml2-dbg "def" (looking-at pml2-non-blank))
        (if (or (looking-at pml2-non-blank)
                 (not (pml2-search-backward-regex-same-lvl pml2-start-def-regex)))
            (+ (current-column) 3) ;; align to the start of the def
          ;; if nothing after "=" or ":" indent from the beginning of the def
          (goto-char (match-end 0))
          (pml2-move-to-delim-or-first)
          (if (equal (match-string 0) ":")
              (+ (current-column) 6)
            (+ (current-column) 2)))))))

;; no matching lines found, we are on a line of lower depth
;; it contains the opening delimiter for the depth of
;; the line being indented
;; TODO: in the case, we lack an extra indentation for the second line
(defun pml2-move-if-not-found (is-case is-semi is-closing line1)
  ;; get the position of this delimiter
  (pml2-dbg "pml2-move-if-not-found" (point) is-case is-semi is-closing line1)
  (let ((pos (car (cdr (syntax-ppss))))
        (line2 nil)
        (may-extra (and (not is-case) (not is-semi) (not is-closing))))
    (setq line2 (line-number-at-pos pos))
    (if pos
        (progn
          (goto-char pos)
          (forward-char)
          ;; if non blank after delim, ident too char after delim
          ;; recall the the line is not a case, semi of def line
          (if (looking-at pml2-non-blank)
              (progn (forward-char)
                     (pml2-dbg "pml2-move-if-not-found non blank" line2)
                     (cons t (+ (current-column)
                                (if (and may-extra
                                         (> line1 line2)) 2 0))))
            ;; otherwise ident relative to the beginning of the line
            (pml2-dbg "pml2-move-if-not-found blank" line2)
            (pml2-move-to-first-non-blank)
            (cons nil (+ (current-column)
                         (if (and may-extra
                                  (> line1 (+ 1 line2))) 2 0)))))
      ;; fall back for depth 0, usefull ?
      (cons nil 0))))

;; function computing the indentation reference,
;; mainly calling the two previous
(defun pml2-search-ref-line ()
  (pml2-move-to-first-non-blank)
  (let ((line (line-number-at-pos))
        (is-closing (pml2-is-closing)))
  (if (or (equal (char-after) ?\;) (equal (char-after) ?|))
      (progn
        (goto-char (car (cdr (syntax-ppss))))
        (cons t (current-column)))
    (if (pml2-is-case)
        (if (pml2-search-backward-regex-same-lvl pml2-case-regex)
            (pml2-move-if-found t nil)
          (pml2-move-if-not-found t nil is-closing line))
      (if (pml2-after-semi)
          (progn
            (goto-char (pml2-after-semi))
            (if (pml2-search-backward-regex-same-lvl pml2-case-or-semi-regex)
                (pml2-move-if-found nil t)
              (pml2-move-if-not-found nil t is-closing line)))
        (if (pml2-search-backward-regex-same-lvl pml2-any-ref-regex)
            (pml2-move-if-found nil nil)
          (pml2-move-if-not-found nil nil is-closing line)))))))

;; compute the diff of parenthesis level of two positions
(defun pml2-indent-level-diff (pos1 pos2)
  "return the difference in indent level of the two point
   or nil if the indent level decrease between the points"
  (save-excursion
    (let ((depth1 (pml2-depth pos1))
          (depth2 (pml2-depth pos2)))
      (- depth2 depth1))))

;; now the main indent function is easy !
(defun pml2-indent-function ()
  (save-excursion
    ;; ppss = parenthesis level computed
    ;; for the line beginning.
    (pml2-move-to-first-non-blank)
    (let ((pos (point))
          (ref nil)
          (lvl 0))
      ;; at top symbol, 0 indent
      (if (pml2-top pos)
          (progn
            (setq lvl 0))
        ;; general case, get column from reference line
        (setq ref (pml2-search-ref-line))
        (if (car ref) ; did we find a reference line ?
            (setq lvl (cdr ref))
          (setq diff (pml2-indent-level-diff (point) pos))
          (setq lvl (+ (cdr ref) (* 2 diff)))))
      (goto-char pos)
      ;; we indent the current line, but also all comments that are before
      (let ((cont t))
        (while (and (> (line-number-at-pos) 1) cont)
          (indent-line-to lvl)
          (pml2-move-to-previous-non-empty-line t)
          (setq cont (looking-at "//")))))))

;; PML program buffer hold the result of the compilation
(defvar pml2-program-buffer nil)

;; Create and/or prepare the buffer for a new compilation
(defun pml2-select-program-buffer ()
  (if (and pml2-program-buffer (buffer-live-p pml2-program-buffer))
      (set-buffer pml2-program-buffer)
    (setq pml2-program-buffer (get-buffer-create "*pml-interaction*"))
    (pop-to-buffer pml2-program-buffer)
    (pml2-mode) ;; for highlighting only
    (comint-mode)
    (make-local-variable 'comint-output-filter-functions)
    (make-local-variable 'comint-exec-hook)
    (local-set-key [(mouse-1)] 'pml2-handle-click)
    (setq comint-output-filter-functions
          (cons 'pml2-filter-comint-output comint-output-filter-functions))
    (setq comint-exec-hook nil))
  (setq pml2-cur-output-pos 0)
  (erase-buffer))

;; OVERLAY managment to display error position in the source file

;; regexp for position
(defvar pml2-pos-regexp
  "\\( [^ ,]+\\), \\([0-9]+\\):\\([0-9]+\\)\\(-\\(\\([0-9]+\\):\\)?\\([0-9]+\\)\\)?")

;; face of error link
(make-face 'pml2-link-face)
(set-face-background 'pml2-link-face "LightBlue")

;; Again a dirty global
(defvar pml2-cur-output-pos 0)

;; function filtering the result of comilation and creating the overlay
(defun pml2-filter-comint-output (output)
  (save-excursion
    (pop-to-buffer pml2-program-buffer)
    (goto-char pml2-cur-output-pos)
    (while (search-forward-regexp pml2-pos-regexp nil t)
      (let
          ((filename (match-string 1))
           (line1 (string-to-number (match-string 2)))
           (col1 (string-to-number (match-string 3)))
           (line2 (match-string 6))
           (col2 (match-string 7)))
        (if (and line2 (not col2))
            (progn (setq col2 line2) (setq line2 nil)))
        (if line2 (setq line2 (string-to-number line2)) (setq line2 line1))
        (if col2 (setq col2 (string-to-number col2)) (setq col2 col1))
        (let ((overlay (make-overlay (+ 1 (match-beginning 0)) (match-end 0))))
          (overlay-put overlay 'position t)
          (overlay-put overlay 'face 'pml2-link-face)
          (overlay-put overlay 'reactive t)
          (overlay-put overlay 'type 'link)
          (overlay-put overlay 'filename filename)
          (overlay-put overlay 'line1 line1)
          (overlay-put overlay 'line2 line2)
          (overlay-put overlay 'col1 col1)
          (overlay-put overlay 'col2 col2))))))

;; search a position overlay among the overlays
(defun pml2-find-pos-overlay (overlay-list)
  (let ((l overlay-list))
    (while (and l (not (overlay-get (car l) 'position)))
      (setq l (cdr l)))
    (car l)))

;; returns the overlays at the position of event
(defsubst pml2-pos-at-event (event)
  (pml2-find-pos-overlay (overlays-at (posn-point (event-start event)))))

;; A global variable because emacs list has dynamic binding
;; and no real closure
;; This overlay show the current position in the source code
(defvar pml2-cur-overlay nil)

;; Delete this overlay (added as a pre-command-hook)
(defun pml2-delete-cur-overlay ()
    (if pml2-cur-overlay (delete-overlay pml2-cur-overlay)))

;; Handle a click on an error position
;; All infos are properties of the overlay
(defun pml2-handle-click (event)
  (interactive "@e")
  (let ((span (pml2-pos-at-event event)))
    (if span
        (let ((filename (overlay-get span 'filename))
              (line1 (overlay-get span 'line1))
              (line2 (overlay-get span 'line2))
              (col1 (overlay-get span 'col1))
              (col2 (overlay-get span 'col2))
              (buffer nil)
              (beg nil)
              (end nil)
              (overlay nil))
          (setq buffer (find-file-noselect filename))
          (switch-to-buffer-other-window buffer)
          (set-buffer buffer)
          (goto-line line1)
          (forward-char (- col1 1))
          (setq beg (point))
          (goto-line line2)
          (forward-char col2)
          (setq end (point))
          (setq overlay (make-overlay beg end))
          (overlay-put overlay 'face 'pml2-link-face)
          (setq pml2-cur-overlay overlay)))))

;; Compilation itself
(defvar pml2-program-name "pml2")

(defun pml2-compile ()
  "compile the current buffer with pml"
  (interactive)
  (save-buffer)
  ;;(setq pml2-last-goal nil)
  ;;(pml2-remove-spans)
  (let ((switches
	 (append (pml2-program-options) (list buffer-file-name))))
    ;;(setq pml2-pending-output "")
    (pml2-select-program-buffer)
    (setq pml2-process
	  (comint-exec pml2-program-buffer "pml-process"
                       pml2-program-name nil switches))
    (display-buffer pml2-program-buffer)))

;; our (small mode map)
(defvar pml2-mode-map
  (let ((pml2-mode-map (make-keymap)))
    (progn
      (define-key pml2-mode-map (kbd "C-c C-c") 'pml2-compile)
;;      (define-key pml-mode-map (kbd "C-c g") 'pml-submit-expr-to-goal)
;;      (define-key pml-mode-map (kbd "C-c r") 'pml-submit-region-to-goal)
;;      (define-key pml-mode-map (kbd "C-c e") 'pml-remove-spans)
;;      (define-key pml-mode-map (kbd "C-c k") 'pml-kill-process)
    pml2-mode-map))
  "Keymap for PML major mode")

;; Menu
(defvar pml2-compile-timed t
  "If t, displays a timing report after the execution")

(defvar pml2-compile-quiet nil
  "If t, disables the printing definition data")

(defvar pml2-compile-log-subtyping nil
  "If t, log subtyping informations")

(defvar pml2-compile-log-compare nil
  "If t, log term comparison")

(defvar pml2-compile-log-ordinal nil
  "If t, log ordinal comparison")

(defvar pml2-compile-log-equivalence nil
  "If t, log equivalence decision")

(defvar pml2-compile-log-full-equivalence nil
  "If t, log details of equivalence decision")

(defvar pml2-compile-log-typing nil
  "If t, log typing informations")

(defvar pml2-compile-log-scp nil
  "If t, log size change principle")

(defvar pml2-compile-log-parsing nil
  "If t, log parsing")

(defvar pml2-compile-log-unif nil
  "If t, log unifications")

(defun pml2-program-options ()
  (let ((switches nil) (logs ""))
    (if pml2-compile-log-subtyping (setq logs (concat "s" logs)))
    (if pml2-compile-log-typing (setq logs (concat "t" logs)))
    (if pml2-compile-log-scp (setq logs (concat "y" logs)))
    (if pml2-compile-log-unif (setq logs (concat "u" logs)))
    (if pml2-compile-log-parsing (setq logs (concat "p" logs)))
    (if pml2-compile-log-compare (setq logs (concat "c" logs)))
    (if pml2-compile-log-equivalence (setq logs (concat "e" logs)))
    (if pml2-compile-log-ordinal (setq logs (concat "o" logs)))
    (if pml2-compile-log-full-equivalence (setq logs (concat "f" logs)))
    (if (not (equal logs "")) (setq switches (cons "--log" (cons logs switches))))
    (if pml2-compile-timed (setq switches (cons "--timed" switches)))
    (if pml2-compile-quiet (setq switches (cons "--quiet" switches)))
    switches))


(defvar pml2-options-list
  '(("Timed" . 'pml2-compile-timed)
    ("Quiet" . 'pml2-compile-quiet)
    ("Log typing" . 'pml2-compile-log-typing)
    ("Log subtyping" . 'pml2-compile-log-subtyping)
    ("Log unifications" . 'pml2-compile-log-unif)
    ("Log size change principle" . 'pml2-compile-log-scp)
    ("Log equivalence decision" . 'pml2-compile-log-equivalence)
    ("Log details of equivalence decision" . 'pml2-compile-log-full-equivalence)
    ("Log term comparison" . 'pml2-compile-log-compare)
    ("Log ordinal comparison" . 'pml2-compile-log-ordinal)
    ("Log parsing" . 'pml2-compile-log-parsing))
  "List of supported toggle options")

(defun pml2-toggle-option (opt)
  (set opt (not (symbol-value opt)))
  (pml2-update-option-menu))

(defun pml2-update-option-menu ()
  (easy-menu-change
   '("PML") "Compiler options"
   (mapcar (lambda (option)
;;	     (message "toggle %S %S" (cdr option) (eval (cdr option)))
	     (vector (car option)
		     (list 'pml2-toggle-option (cdr option))
		     ':style 'toggle
		     ':selected (nth 1 (cdr option))
		     ':active t))
	   pml2-options-list)))


(defun pml2-build-menu ()
  (easy-menu-define
   pml2-mode-menu (list pml2-mode-map)
   "PML Mode Menu."
   '("PML"
     ["Compile..." pml2-compile t]
     ("Compiler options" ["Dummy" nil t])
     ["Indent" indent-region t]))
  (easy-menu-add pml2-mode-menu)
  (pml2-update-option-menu))


;; the main function creating the mode
(define-derived-mode pml2-mode fundamental-mode "Pml2"
  "A major mode for editing Pml2 files."
  (set-syntax-table pml2-mode-syntax-table)
  (setq-local font-lock-defaults '(pml2-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-default indent-tabs-mode nil)
  (set-input-method "Pml2")
  (pml2-build-menu)
  ;;(setq-local imenu-generic-expression
  ;;pml2-imenu-generic-expression)
  ;;(setq-local outline-regexp pml2-outline-regexp)
  (use-local-map pml2-mode-map)
  (add-hook 'pre-command-hook 'pml2-delete-cur-overlay)
  ;; Indentation
  (set (make-local-variable 'indent-line-function) #'pml2-indent-function))

;; register mode the the .pml extension
(add-to-list 'auto-mode-alist '("\\.pml\\'" . pml2-mode))

;;; pml2.el ends here
