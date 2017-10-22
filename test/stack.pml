include lib.option

type stack_sig_aux<stack:ο→ο> =
  { empty : ∀a, stack<a>
  ; push  : ∀a, a ⇒ stack<a> ⇒ stack<a>
  ; pop   : ∀a, stack<a> ⇒ option<a * stack<a>> }

type stack_sig = ∃stack:ο→ο, stack_sig_aux<stack>

include lib.list

val stack_impl : stack_sig =
  { empty = nil
  ; push  = fun e s { e :: s }
  ; pop   = fun s { case s { [] → None | e :: s → Some[(e, s)] } } }
