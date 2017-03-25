
type rec tree23<a:ο> = [
  E ;
  N2 of { l : tree23; x : a; r : tree23 } ;
  N3 of { l : tree23; x : a; m : tree23; y : a; r : tree23 } ]

type cmp = [ Le ; Eq ; Ge ]

val rec mem : ∀a:ο, ∀f∈(a⇒a⇒cmp), ∀x∈a, ∀t∈tree23<a>, bool = fun f x t →
  case t {
  | E[] → false
  | N2[c] →
     case f x c.x {
     | Le[] → mem f x c.l
     | Eq[] → true
     | Ge[] → mem f x c.r }
  | N3[c] →
     case f x c.x {
     | Le[] → mem f x c.l
     | Eq[] → true
     | Ge[] →
     case f x c.y {
     | Le[] → mem f x c.m
     | Eq[] → true
     | Ge[] → mem f x c.r }}
  }

type add23<a:ο> = [
  N1 of tree23<a> ;
  N2 of { l : tree23<a>; x : a; r : tree23<a> } ]

val rec add_aux : ∀a:ο, ∀f∈(a⇒a⇒cmp), ∀x∈a, ∀t∈tree23<a>, add23<a> = fun f x t →
  case t {
  | E[] → N2[{l=E; x=x; r=E}]
  | N2[c] →
     case f x c.x {
     | Le[] → case add_aux f x c.l {
              | N1[t] → N1[N2[{l=t;x=c.x;r=c.r}]]
              | N2[n] → N1[N3[{l=n.l;x=n.x;m=n.r;y=c.x;r=c.r}]]
              }
     | Eq[] → N1[t]
     | Ge[] → case add_aux f x c.l {
              | N1[t] → N1[N2[{l=c.l;x=c.x;r=t}]]
              | N2[n] → N1[N3[{l=c.l;x=c.x;m=n.l;y=n.x;r=n.r}]]
              }}
  | N3[c] →
     case f x c.x {
     | Le[] → case add_aux f x c.l {
              | N1[t] → N1[N3[{l=t;x=c.x;m=c.m;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=n.l;x=n.x;r=n.r}]
                           ;x=c.x
                           ;r=N2[{l=c.m;x=c.y;r=c.r}]}]
              }
     | Eq[] → N1[t]
     | Ge[] →
     case f x c.y {
     | Le[] → case add_aux f x c.l {
              | N1[t] → N1[N3[{l=c.l;x=c.x;m=t;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=c.l;x=c.x;r=n.l}]
                           ;x=n.x
                           ;r=N2[{l=n.r;x=c.y;r=c.r}]}]
              }
     | Eq[] → N1[t]
     | Ge[] → case add_aux f x c.l {
              | N1[t] → N1[N3[{l=c.l;x=c.x;m=t;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=c.l;x=c.x;r=c.m}]
                           ;x=c.y
                           ;r=N2[{l=n.l;x=n.x;r=n.r}]}]
              }}}
  }


val add : ∀a:ο, ∀f∈(a⇒a⇒cmp), ∀x∈a, ∀t∈tree23<a>, tree23<a> = fun f x t →
  case add_aux f x t {
  | N1[t] → t
  | N2[c] → N2[c] }
