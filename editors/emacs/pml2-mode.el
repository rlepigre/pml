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


 ;;;###autoload
(define-derived-mode pml2-mode fundamental-mode "Pml2"
  "A major mode for editing Pml2 files."
  (set-syntax-table pml2-mode-syntax-table)
  (setq-local font-lock-defaults '(pml2-font-lock-keywords))
  (setq-local comment-start "//")
  ;(setq-local font-lock-defaults
  ;            '(pml2-font-lock-keywords))
  (setq-local indent-line-function 'pml2-indent-line)
  (set-input-method "Pml2")
                                        ;(setq-local imenu-generic-expression
                                        ;pml2-imenu-generic-expression)
                                        ;(setq-local outline-regexp pml2-outline-regexp)
  )

 ;;; Indentation

                                        ; (defun pml2-indent-line ()
                                        ;   "Indent current line of Pml2 code."
                                        ;   (interactive)
                                        ;   (let ((savep (> (current-column) (current-indentation)))
;;       (indent (condition-case nil (max (pml2-calculate-indentation) 0)
;;                 (error 0))))
;;     (if savep
;;       (save-excursion (indent-line-to indent))
;;       (indent-line-to indent))))

;; (defun pml2-calculate-indentation ()
;;   "Return the column to which the current line should be indented."
;;   ...)

(add-to-list 'auto-mode-alist '("\\.pml\\'" . pml2-mode))

 ;;; pml2.el ends here
