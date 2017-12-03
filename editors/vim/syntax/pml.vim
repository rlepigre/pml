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
syntax keyword Keyword check for because delim set assume suppose take
syntax match   Keyword "λ"
syntax match   Keyword "μ"
syntax match   Keyword "ν"
syntax match   Keyword "Λ"
syntax match   Keyword "[][{}()=<>,;:.|]"
syntax match   Keyword "⇒"
syntax match   Keyword "→"
syntax match   Keyword "×"
syntax match   Keyword "∈"

" Constructors
syntax match Constant "\<\u\w*\>"
syntax match Constant "\<true\>"
syntax match Constant "\<false\>"

" Include
syntax match Include "\<include \w*\(\.\w*\)*"

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

" Abbreviations
abbreviate ->        →
abbreviate =>        ⇒
abbreviate *         ×
abbreviate <iota>    ι
abbreviate <value>   ι
abbreviate <tau>     τ
abbreviate <term>    τ
abbreviate <sigma>   σ
abbreviate <stack>   σ
abbreviate <omicron> ο
abbreviate <prop>    ο
abbreviate <kappa>   κ
abbreviate <ordinal> κ
