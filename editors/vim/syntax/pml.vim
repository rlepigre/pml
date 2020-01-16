" Vim syntax file
" Language:        PML
" Maintainer:      Rodolphe Lepigre <rodolphe.lepigre@univ-smb.fr>
" Last Change:     17/09/2016
" Version:         1.0
" Original Author: Rodolphe Lepigre <rodolphe.lepigre@univ-smb.fr>

if exists("b:current_syntax")
  finish
endif

" Comments
syn keyword Todo contained TODO FIXME NOTE
syn region Comment start="//" end="$" contains=Todo

syntax region Str start=/\v"/ skip=/\v\\./ end=/\v"/
highlight link Str Character

" Keywords
syntax keyword Keyword fun save restore case of fix let rec corec using use
syntax keyword Keyword type def val sort if else deduce show qed such that
syntax keyword Keyword check for because delim set assume suppose take print
syntax keyword Keyword auto log showing force lazy
syntax match   Keyword "λ"
syntax match   Keyword "μ"
syntax match   Keyword "ν"
syntax match   Keyword "Λ"
syntax match   Keyword "[][{}()=,;:.|]"
syntax match   Keyword "∃"
syntax match   Keyword "∀"
syntax match   Keyword "⇒"
syntax match   Keyword "→"
syntax match   Keyword "⇏"
syntax match   Keyword "↛"
syntax match   Keyword "×"
syntax match   Keyword "∈"
syntax match   Keyword "\^"
syntax match   Keyword "⟨"
syntax match   Keyword "⟩"
syntax match   Keyword "⋯"
syntax match   Keyword "+ₒ"

" Constructors
syntax match Constant "\<\u\w*\>"
syntax match Constant "\<true\>"
syntax match Constant "\<false\>"
syntax match Constant "\<\d\d*\>"

" Include
syntax match Include "\<include \w*\(\.\w*\)*"

" Operator configuration
syntax keyword Include infix
syntax match Include "\<priority \d\d*"
syntax match Include "\<left associative"
syntax match Include "\<right associative"

" Meta-variables
syntax match Include "{-[ ]*\w*[ ]*-}"

" Sorts
syntax match Type "ι"
syntax match Type "<iota>"
syntax match Type "<value>"
syntax match Type "τ"
syntax match Type "<tau>"
syntax match Type "<term>"
syntax match Type "σ"
syntax match Type "<sigma>"
syntax match Type "<stack>"
syntax match Type "ο"
syntax match Type "<omicron>"
syntax match Type "<prop>"
syntax match Type "κ"
syntax match Type "<kappa>"
syntax match Type "<ordinal>"

" A few functions to work with abbreviations (input mode).
func Eatspace()
  let c = nr2char(getchar(0))
  return (c =~ '\s') ? '' : c
endfunc

function! s:Expr(default, repl)
  if getline('.')[col('.')-2]=='\'
    return "\<bs>".a:repl
  else
    return a:default
  endif
endfunction

function! s:DefAB(lhs, rhs)
  exe 'ab '.a:lhs.' <c-r>=<sid>Expr('.string(a:lhs).', '.string(a:rhs).')<cr>'
endfunction

function! s:DefABEat(lhs, rhs)
  exe 'ab '.a:lhs.' <c-r>=<sid>Expr('.string(a:lhs).', '.string(a:rhs).')<cr><c-r>=Eatspace()<cr>'
endfunction

command! -nargs=+ ABBackslash    call s:DefAB(<f-args>)
command! -nargs=+ ABBackslashEat call s:DefABEat(<f-args>)

" Usual abbreviations.
ab -> →
ab => ⇒
ab -|> ↛
ab =|> ⇏
ab *  ×
ab +o +ₒ

" Abbreviations starting with backslash.
ABBackslashEat langle  ⟨
ABBackslash    rangle  ⟩
ABBackslash    notin   ∉
ABBackslash    times   ×
ABBackslashEat forall  ∀
ABBackslashEat exists  ∃
ABBackslash    infty   ∞
ABBackslashEat mu      μ
ABBackslashEat nu      ν
ABBackslash    iota    ι
ABBackslash    tau     τ
ABBackslash    sigma   σ
ABBackslash    omicron ο
ABBackslash    kappa   κ
ABBackslashEat dots    ⋯
