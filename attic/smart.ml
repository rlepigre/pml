(** {5 other constructors} *)
let uwit : type a. popt -> tbox -> strloc -> a sort -> (a var -> pbox)
             -> a box =
  fun p t x s f ->
    let b = vbind (mk_free s) x.elt f in
    box_apply2 (fun t b -> Pos.make p (UWit(s, t, (x.pos, b)))) t b

let ewit : type a. popt -> tbox -> strloc -> a sort -> (a var -> pbox)
             -> a box =
  fun p t x s f ->
    let b = vbind (mk_free s) x.elt f in
    box_apply2 (fun t b -> Pos.make p (EWit(s, t, (x.pos, b)))) t b

let owmu : popt -> obox -> tbox -> strloc -> (ovar -> pbox) -> obox =
  fun p o t x f ->
    let b = vbind (mk_free O) x.elt f in
    box_apply3 (fun o t b -> Pos.make p (OWMu(o,t,(x.pos, b)))) o t b

let ownu : popt -> obox -> tbox -> strloc -> (ovar -> pbox) -> obox =
  fun p o t x f ->
    let b = vbind (mk_free O) x.elt f in
    box_apply3 (fun o t b -> Pos.make p (OWNu(o,t,(x.pos, b)))) o t b

let osch : type a. popt -> obox option -> int -> schema Bindlib.bindbox
                -> obox =
  fun p o i sch ->
    box_apply2 (fun o sch -> Pos.make p (OSch(o,i,sch))) (box_opt o) sch
