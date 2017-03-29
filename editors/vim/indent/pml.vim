" Vim indent file
" Language:     PML2
" Maintainers:  Rodolphe Lepigre <rodolphe.lepigre@univ-smb.fr>
" URL:          http://lama.univ-savoie.fr/~lepigre
" Last Change:  2017 Mar 28


" Only load this indent file when no other was loaded.
if exists("b:did_indent")
 finish
endif
let b:did_indent = 1

setlocal expandtab
setlocal indentexpr=GetPMLIndent()
setlocal indentkeys+=0=else,0=if,0=in,0=let,0=type,0=val,0>},0\|,0}
setlocal nolisp
setlocal nosmartindent
setlocal textwidth=78


" Only define the function once.
if exists("*GetPMLIndent")
  finish
endif

function! GetPMLIndent()
  " At the start of the file use zero indent.
  if lnum == 0
    return 0
  endif

  let lline = getline(v:lnum - 1)
  let cline = getline(v:lnum)
  let ind = indent(v:lnum - 1)

  " If the previous line ended with an arrow, indent.
  if lline =~ '.*→$'
    return ind + 2
  endif

  " If the previous line ended with '{' or '=' indent.
  if lline =~ '.*[{=]$'
    return ind + 2
  endif

  " If the previous line ended with 'in', find the let and indent.
  if lline =~ '.* in$'
    call search('\<in\>', 'bW')
    call searchpairpos('\<let\>', '', '\<in\>', 'bW')
    return virtcol('.') - 1
  endif

  " Defaults to zero.
  return ind

endfunction
