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

" Keywords
syntax keyword Keyword sort def val fun save case of fix
syntax match   Keyword "λ"
syntax match   Keyword "μ"
syntax match   Keyword "ν"
syntax match   Keyword "Λ"
syntax match   Keyword "[][{}()=<>,:.|]"
syntax match   Keyword "⇒"
syntax match   Keyword "→"
syntax match   Keyword "∈"

" Constructors
syntax match Constant "\<\u\w*\>"

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
