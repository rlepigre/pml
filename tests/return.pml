include lib.nat
include lib.list

val prod : list⟨nat⟩ ⇒ nat = fun l {
  delim save return {
    let rec fn : nat ⇒ list⟨nat⟩ → nat = fun acc l {
      case l {
        [] → 1
        x::l → if is_zero x { restore return 0 } else fn (x * acc) l
      }};
    fn 1 l}}