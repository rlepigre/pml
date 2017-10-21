include lib.option

type stack_sig_aux<stack:ο→ο> =
  { empty : ∀a, stack<a>
  ; push  : ∀a, a ⇒ stack<a> ⇒ stack<a>
  ; pop   : ∀a, stack<a> ⇒ option<a> }

type stack_sig = ∃stack:ο→ο, stack_sig_aux<stack>

include lib.list

val stack_impl : stack_sig = // should work
//val stack_impl : stack_sig_aux<list> = // works
  ({ empty = Nil
   ; push  = fun e s { Cons[{hd = e; tl = s}] }
   ; pop   = fun s { case s { Nil → None | Cons[c] → Some[c.hd] } } }
  : stack_sig_aux<list>)
