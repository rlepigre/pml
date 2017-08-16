(provide 'pml2-mode)

(defvar pml2-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [foo] 'pml2-do-foo)
    map)
  "Keymap for `pml2-mode'.")

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
				    "include" "type" "if" "else" "check"
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

(defun pml2-closing ()
  (or
   (equal (buffer-substring (point) (+ (point) 3)) "def")
   (equal (buffer-substring (point) (+ (point) 3)) "val")
   (equal (buffer-substring (point) (+ (point) 4)) "type")
   (equal (char-after) ?|)
   (equal (char-after) ?\;)
   (equal (char-after) ?\))
   (equal (char-after) ?\])
   (equal (char-after) ?})
;   (let ((pos
;          (search-forward-regexp "\\(→\\)\\|\n" nil t)))
;     (message (int-to-string depth))
;     (message (int-to-string (car (syntax-ppss))))
;     (message (buffer-substring (- pos 1) pos))
;     (and (equal (car (syntax-ppss)) depth)
;          (equal (buffer-substring (- pos 1) pos) "→")))
   ))

(defun pml2-is-comment ()
       (equal (buffer-substring (point) (+ (point) 2)) "//"))

; move to the first non blank char at the beginning of a
; line. Return nil if the line has only blank
(defun pml2-move-to-first-non-blank ()
       (end-of-line)
       (setq pos2 (point))
       (beginning-of-line)
       (if (search-forward-regexp "[^ \t\n\r]" pos2 t)
         (progn (backward-char) t)))

(defconst begin-decl-regexp
  "\\(val\\)\\|\\(type\\)\\|\\(def\\)")

(defconst let-in
  "\\(let\\)\\|\\(in\\)")

(defun pml2-indent-function ()
  (save-excursion
                                        ; ppss = parenthesis level computed
                                        ; for the line beginning.
    (beginning-of-line)
    (let ((pos (point))
          (line (line-number-at-pos))
          (pos-min 0)
          (line-min 0)
          (ppss (syntax-ppss)))
      (search-backward-regexp begin-decl-regexp)
      (setq pos-min (point))
      (setq line-min (line-number-at-pos))
      (setq plvl (+ 2 (* 2 (car ppss))))
      (goto-char pos)
      (pml2-move-to-first-non-blank)
      (if (pml2-opening) (setq plvl (+ plvl 2)))
      (if (pml2-closing) (setq plvl (- plvl 2)))
      (pml2-move-to-first-non-blank)
      (if (not (equal (buffer-substring (point) (+ (point) 2)) "in"))
          (progn
            (search-backward-regexp let-in (car (cdr ppss)) t)
            (if (equal (buffer-substring (point) (+ (point) 3)) "let")
                (setq plvl (+ plvl 2))))) ; TODO nested lets like: let let in in
      (goto-char pos)
      (indent-line-to plvl))))


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

  (set (make-local-variable 'indent-line-function) #'pml2-indent-function))

(add-to-list 'auto-mode-alist '("\\.pml\\'" . pml2-mode))

;;; pml2.el ends here
