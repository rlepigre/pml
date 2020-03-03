open Extra
open Bindlib
open Sorts
open Pos
open Ast
open Mapper

let box_closure: type a. a ex loc -> a ebox * t var array * v var array
                                     * t ex loc array * v ex loc array
  = fun e ->
    let vl : v ex loc list ref = ref [] in
    let tl : t ex loc list ref = ref [] in
    let vv = ref [] in
    let tv = ref [] in
    let mapper : type a. recall -> a ex loc -> a ebox = fun {default} e ->
      let s, e = sort e in
      let svl = !vl and stl = !tl and svv = !vv and stv = !tv in
      let e' = default e in
      match is_closed e', s with
      | true, V ->
         vl := svl; tl := stl; vv := svv; tv := stv;
         let v = new_var (mk_free V) "v" in
         vl := e :: !vl;
         vv := v :: !vv;
         box (Pos.none (mk_free V v))
      | true, T ->
         vl := svl; tl := stl; vv := svv; tv := stv;
         let v = new_var (mk_free T) "v" in
         tl := e :: !tl;
         tv := v :: !tv;
         box (Pos.none (mk_free T v))
      | _ -> e'
    in
    let e = map ~mapper:{mapper} e in
    let tl = Array.of_list !tl in
    let vl = Array.of_list !vl in
    let tv = Array.of_list !tv in
    let vv = Array.of_list !vv in
    (lift (unbox e),tv,vv,tl,vl)

type 'a closure =
  (v ex, (t ex, 'a) mbinder) mbinder * v ex loc array * t ex loc array


let make_closure : type a. a ex loc -> a ex loc closure = fun e ->
  let (e,tv,vv,tl,vl) = box_closure e in
  (unbox (bind_mvar vv (bind_mvar tv e)), vl, tl)

let make_bndr_closure
    : type a b. a sort -> (a, b) bndr -> (a, b) bndr closure
  = fun s b0 ->
    let (x,e) = bndr_open b0 in
    let (e,tv,vv,tl,vl) = box_closure e in
    let b = bind_var x e in
    let b = box_pair (box (fst b0)) b in
    (unbox (bind_mvar vv (bind_mvar tv b)), vl, tl)
