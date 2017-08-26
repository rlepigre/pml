(provide 'pml2-mode)

(defvar pml2-mode-syntax-table
  (let ((pml2-mode-syntax-table (make-syntax-table)))

    ; This is added so entity names with underscores can be more easily parsed
    (modify-syntax-entry ?_ "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?' "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?( "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?{ "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?[ "(" pml2-mode-syntax-table)
    (modify-syntax-entry ?) ")" pml2-mode-syntax-table)
    (modify-syntax-entry ?} ")" pml2-mode-syntax-table)
    (modify-syntax-entry ?] ")" pml2-mode-syntax-table)
    ; comments definition
    ; . means punctuation
    ; // 12 means first and second char of one line comments
    ; The second space charater is ignored
    (modify-syntax-entry ?/ ". 12" pml2-mode-syntax-table)
    ; newlines end comments
    (modify-syntax-entry ?\n ">" pml2-mode-syntax-table)
    pml2-mode-syntax-table)
  "Syntax table for pml2-mode")

(defconst pml2-font-lock-keywords
  (list (cons (concat "\\<"
		      (regexp-opt '("case" "of" "val" "let" "in" "rec" "fun" "eval"
				    "include" "type" "if" "else" "check" "save"
                                    "restore" "use" "then" "qed" "from"
                                    "fix" "unfold" "clear" "quit" "parse" "latex"
                                    "exit" "set" "html" "such" "that" "abort"
				    "def" "sort" "show" "deduce" "using"))
                      "\\>") ; FIXME
              'font-lock-keyword-face)
        )
  "Minimal highlighting expressions for pml2 mode.")

(require 'quail)
(quail-define-package
 "Pml2" "Pml2" "x⃗" t
 "A transliteration scheme for Pml2."
 nil t t t t nil t nil nil nil t)
(quail-define-rules
 ("->" ?→)      ("\\to" ?→)
 ("=>" ?⇒)      ("\\To" ?⇒)
 ("8<" ?✂)
 ("==" ?≡)      ("\\equiv" ?≡)
 ("!=" ?≠)      ("\\notequiv" ?≠)
 ("\\l" ?λ)     ("\\lambda" ?λ)
 ("\\L" ?Λ)     ("\\Lambda" ?Λ)
 ("\\m" ?μ)     ("\\mu" ?μ)
 ("\\n" ?ν)     ("\\nu" ?ν)
 ("\\o" ?ο)     ("\\omicron" ?ο)
 ("\\t" ?τ)     ("\\tau" ?τ)
 ("\\i" ?ι)     ("\\iota" ?ι)
 ("\\v" ?↓)     ("\\downarrow" ?↓)
 ("\\s" ?σ)     ("\\sigme" ?σ)
 ("\\e" ?κ)     ("\\kappa" ?κ)
 ("\\8" ?∞)     ("\\infty" ?∞)
 ("\\A" ?∀)     ("\\forall" ?∀)
 ("\\E" ?∃)     ("\\exists" ?∃)
 ("\\in" ?∈)
 ("\\ni" ?∉)    ("\\notin" ?∉)
 ("\\*" ?×)     ("\\times" ?×)
 ("\\<" ?⊂)     ("\\subset" ?⊂)

)

; test if current position must be indented in a fixed
; from the parenthesis level
(defun pml2-opening ()
  (or
   (equal (char-after) ?\()
   (equal (char-after) ?\[)
   (equal (char-after) ?{)))

(defun pml2-closing (depth)
  (save-excursion
    (or
     (equal (buffer-substring (point) (+ (point) 3)) "def")
     (equal (buffer-substring (point) (+ (point) 3)) "val")
     (equal (buffer-substring (point) (+ (point) 4)) "type")
     (equal (char-after) ?|)
     (equal (char-after) ?\;)
     (equal (char-after) ?\))
     (equal (char-after) ?\])
     (equal (char-after) ?})
     (let ((pos
            (search-forward-regexp "\\(→\\)\\|\n" nil t)))
       (and (equal (car (syntax-ppss pos)) depth)
            (equal (buffer-substring (- pos 1) pos) "→")))
     )))

; move to the first non blank char at the beginning of a
; line. Return nil if the line has only blank
(defun pml2-move-to-first-non-blank ()
       (end-of-line)
       (setq pos2 (point))
       (beginning-of-line)
       (if (search-forward-regexp "[^ \t\n\r]" pos2 t)
         (progn (backward-char) t)))

(defconst let-in
  "\\(let\\)\\|\\(type\\)\\|\\(val\\)\\|\\(def\\)\\|\\(in\\)\\|=")

(defun pml2-is-delim-case (pos)
  (save-excursion
    (goto-char pos)
    (let ((ppss (syntax-ppss))
          (curdepth 0)
          (limit 0)
          (depth 0))
      (setq limit (car (cdr ppss)))
      (setq depth (car ppss))
      (setq curdepth (+ depth 1))
      (while (> curdepth depth)
          (if (search-backward "case" limit t)
              (setq curdepth (car (syntax-ppss)))
            (setq curdepth -1)))
      (eq curdepth depth))))

(defun pml2-depth (ppss)
  (save-excursion
    (if (and ppss (car ppss))
        (+
         (if (pml2-is-delim-case (- (car ppss) 1))
             4 2)
         (pml2-depth (cdr (syntax-ppss (- (car ppss) 1)))))
      2)))

(defun pml2-indent-function ()
  (save-excursion
                                        ; ppss = parenthesis level computed
                                        ; for the line beginning.
    (pml2-move-to-first-non-blank)
    (let ((pos (point))
          (ppss (syntax-ppss)))
      (setq plvl (pml2-depth (cdr ppss)))
      (if (pml2-opening) (setq plvl (+ plvl 2)))
      (if (pml2-closing (car ppss)) (setq plvl (- plvl 2)))
      (goto-char pos)
      (indent-line-to plvl))))

(defvar pml2-program-buffer nil)

(defvar pml2-cur-output-pos 0)

(defvar pml2-pos-regexp
  "\\( [^ ,]+\\), \\([0-9]+\\):\\([0-9]+\\)\\(-\\(\\([0-9]+\\):\\)?\\([0-9]+\\)\\)?")

(make-face 'pml2-link-face)

(set-face-background 'pml2-link-face "LightBlue")

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

(defun pml2-find-pos-overlay (overlay-list)
  (let ((l overlay-list))
    (while (and l (not (overlay-get (car l) 'position)))
      (setq l (cdr l)))
    (car l)))

(defsubst pml2-pos-at-event (event)
  (pml2-find-pos-overlay (overlays-at (posn-point (event-start event)))))

(defvar pml2-cur-overlay nil)

(defun pml2-delete-cur-overlay ()
    (if pml2-cur-overlay (delete-overlay pml2-cur-overlay)))

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
          (print filename)
          (print line1)
          (print col1)
          (print line2)
          (print col2)
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

(defun pml2-select-program-buffer ()
  (if (and pml2-program-buffer (buffer-live-p pml2-program-buffer))
      (set-buffer pml2-program-buffer)
    (setq pml2-program-buffer (get-buffer-create "*pml-interaction*"))
    (pop-to-buffer pml2-program-buffer)
    (comint-mode)
    (make-local-variable 'comint-output-filter-functions)
    (make-local-variable 'comint-exec-hook)
    (local-set-key [(mouse-1)] 'pml2-handle-click)
    (setq comint-output-filter-functions
          (cons 'pml2-filter-comint-output comint-output-filter-functions))
    (setq comint-exec-hook nil))
  (setq pml2-cur-output-pos 0)
  (erase-buffer))

(defvar pml2-program-name "pml2")

(defvar pml2-program-options nil)

(defun pml2-compile ()
  "compile the current buffer with pml"
  (interactive)
  (save-buffer)
  ;(setq pml2-last-goal nil)
  ;(pml2-remove-spans)
  (let ((switches
	 (append pml2-program-options (list buffer-file-name))))
    ;(setq pml2-pending-output "")
    (pml2-select-program-buffer)
    (cd "/home/raffalli/Caml/pml2_rodolphe") ; FIXME
    (setq pml2-process
	  (comint-exec pml2-program-buffer "pml-process" pml2-program-name nil switches))
    (display-buffer pml2-program-buffer)))

(defvar pml2-mode-map
  (let ((pml2-mode-map (make-keymap)))
    (progn
      (define-key pml2-mode-map (kbd "C-c C-c") 'pml2-compile)
;      (define-key pml-mode-map (kbd "C-c g") 'pml-submit-expr-to-goal)
;      (define-key pml-mode-map (kbd "C-c r") 'pml-submit-region-to-goal)
;      (define-key pml-mode-map (kbd "C-c e") 'pml-remove-spans)
;      (define-key pml-mode-map (kbd "C-c k") 'pml-kill-process)
;      (define-key pml-mode-map (kbd "RET") 'pml-newline-copy-indent)
;      (define-key pml-mode-map (kbd "TAB") 'pml-forward-indent)
;      (define-key pml-mode-map (kbd "C-TAB") 'pml-backward-indent)
;      (define-key pml-mode-map (kbd "C-S-TAB") 'pml-indent-line)
;      (if is-xemacs
;	  (define-key pml-mode-map [(meta shift button1)] 'pml-handle-click))
    pml2-mode-map))
  "Keymap for PML major mode")

 ;;;###autoload
(define-derived-mode pml2-mode fundamental-mode "Pml2"
  "A major mode for editing Pml2 files."
  (set-syntax-table pml2-mode-syntax-table)
  (setq-local font-lock-defaults '(pml2-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-default indent-tabs-mode nil)
  ;(setq-local font-lock-defaults
  ;            '(pml2-font-lock-keywords))
  (set-input-method "Pml2")
  ;(setq-local imenu-generic-expression
  ;pml2-imenu-generic-expression)
  ;(setq-local outline-regexp pml2-outline-regexp)
  ;;; Indentation
  (use-local-map pml2-mode-map)
  (add-hook 'pre-command-hook pml2-delete-cur-overlay)
  (set (make-local-variable 'indent-line-function) #'pml2-indent-function))

(add-to-list 'auto-mode-alist '("\\.pml\\'" . pml2-mode))

;;; pml2.el ends here
