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
    (modify-syntax-entry ?) "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?} "w" pml2-mode-syntax-table)
    (modify-syntax-entry ?] "w" pml2-mode-syntax-table)
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
(defun lvl-keyword ()
       (or
            (equal (char-after) ?|)
            (equal (char-after) ?\;)
            (equal (char-after) ?\))
            (equal (char-after) ?])
            (equal (char-after) ?})
            (equal (buffer-substring (point) (+ (point) 3)) "def")
            (equal (buffer-substring (point) (+ (point) 3)) "val")
            (equal (buffer-substring (point) (+ (point) 4)) "type")))

; move to the first non blank char at the beginning of a
; line. Return nil if the line has only blank
(defun move-to-first-non-blank ()
       (end-of-line)
       (setq pos2 (point))
       (beginning-of-line)
       (if (search-forward-regexp "[^ \t\n\r]" pos2 t)
         (progn (backward-char) t)))


(defun pml2-indent-function ()
       (save-excursion
            ; ppss = parenthesis level computed
            ; for the line beginning.
            (beginning-of-line)
	    (let ((ppss (syntax-ppss))
		  (pos1 (point))
		  (lvl nil)
		  (pos2 nil)
		  (pos3 nil))
		 (setq lvl (car ppss))
                 ; special cases indented directly from lvl
                 (move-to-first-non-blank)
		 (if (lvl-keyword)
                     (indent-line-to (* 2 lvl))
                 ; general cases indented from the previous
                 ; non empty line
                 (previous-line)
                 (while (not (move-to-first-non-blank)) (previous-line))
		 (setq pos3 (point))
  		 (beginning-of-line)
		 (setq pos2 (point))
                 ; indent on the chat after the keywords below,
                 ; if the line is non empty
		 (if (search-forward-regexp
		          "\\(\\(→\\)\\|\\(⇒\\)\\)[ \t]*[^ \t\n\r]"
		          pos1 t)
		     (setq pos3 (- (match-end 0) 1)))
		 (setq pos3 (- pos3 pos2))
		 (setq pos3 (max pos3 (+ 2 (* 2 lvl))))
		 (goto-char pos1)
		 (indent-line-to pos3)))))

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
