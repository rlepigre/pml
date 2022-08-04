
type rec nat = [ Z ; S of nat ]

val rec fg : { f : nat ⇒ nat ;
               g : nat ⇒ nat }
  = { f = fun x { S[fg.g x] }
    , g = fun x { case x { Z → Z
                           S[x] → fg.f x } }}