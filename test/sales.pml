include lib.nat
include lib.nat_proofs
include lib.list

type product = { id : nat; price : nat}
type order   = list⟨product × nat⟩

val rec price : order ⇒ nat =
  fun ord {
    case ord {
      []      → 0
      o::rest → let (prd, qty) = o; qty * prd.price + price rest
    }
  }

val rec add_order : product ⇒ nat ⇒ order ⇒ order =
  fun prd qty ord {
    case ord {
      []      → (prd, qty) :: []
      o::rest → let (prd', qty') = o;
                if eq prd.id prd'.id { (prd, qty+qty' ) :: rest }
                  else { o :: add_order prd qty rest }
    }
  }

val rec correct : ∀p∈product,∀q∈nat,∀o∈order,
  price (add_order p q o) ≡ q * p.price + price o =
   fun prd qty ord {
     case ord {
       []      → qed
       o::rest →
         let (prd', qty') = o;
         use correct prd qty rest;
         if eq prd.id prd'.id {
             deduce price (add_order prd qty ord) ≡
               (qty + qty') * prd.price + price rest;
           {--}
         }
           else {
             deduce price (add_order prd qty ord) ≡
               qty' * prd'.price + price (add_order prd qty rest);
             showing qty' * prd'.price + (qty * prd.price + price rest) ≡
               qty * prd.price + ( qty' * prd'.price + price rest);
             use add_assoc (qty' *prd'.price) (qty * prd.price) (price rest);
             use add_assoc (qty * prd.price) (qty' *prd'.price) (price rest);
             use add_comm (qty * prd.price) (qty' *prd'.price);
             qed
           }
     }
   }
