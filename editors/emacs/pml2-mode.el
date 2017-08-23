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
                                    "restore" "use"
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

(defvar pml2-program-buffer
  nil)

(defun pml2-select-program-buffer ()
  (if (and pml2-program-buffer (buffer-live-p pml2-program-buffer))
      (set-buffer pml2-program-buffer)
    (progn
      (setq pml2-program-buffer (get-buffer-create "*pml-interaction*"))
      (pop-to-buffer pml2-program-buffer)
      (comint-mode)
      (make-local-variable 'comint-output-filter-functions)
      (make-local-variable 'comint-exec-hook)
      ;(setq comint-output-filter-functions
	;    '(comint-postoutput-scroll-to-bottom pml2-filter-comint-output))
      (setq comint-exec-hook nil))))

(defvar pml2-program-name
  "/home/raffalli/Caml/pml2_rodolphe/main.native") ; FIXME

(defvar pml2-program-options
  nil)

(defvar pml2-program-buffer
  nil)

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
;    (display-progress-feedback 'pml2-compilation (concat "compiling: " buffer-file-name))
    (process-send-string pml2-process "\n")))

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
  (set (make-local-variable 'indent-line-function) #'pml2-indent-function))

(add-to-list 'auto-mode-alist '("\\.pml\\'" . pml2-mode))

;;; pml2.el ends here
