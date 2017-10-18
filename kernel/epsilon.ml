open Ast
open Compare
open Uvars
open Sorts
open Pos

let owmu_counter = ref (-1)
let ownu_counter = ref (-1)
let osch_counter = ref (-1)

module VWitHash = Hashtbl.Make(VWit)
let vwit_hash    = VWitHash.create 256

let swit_counter = ref (-1)
let uwit_counter = ref (-1)
let ewit_counter = ref (-1)

let reset_counters : unit -> unit = fun () ->
  owmu_counter := (-1); ownu_counter := (-1); osch_counter := (-1);
  swit_counter := (-1); uwit_counter := (-1);
  ewit_counter := (-1)

let owmu : ordi -> term -> (o, p) bndr -> ordi =
  fun o t b -> incr owmu_counter; Pos.none (OWMu(!owmu_counter, (o,t,b)))

let ownu : ordi -> term -> (o, p) bndr -> ordi =
  fun o t b -> incr ownu_counter; Pos.none (OWNu(!ownu_counter, (o,t,b)))

let osch : ordi option -> int -> schema -> ordi =
  fun o i s -> incr osch_counter; Pos.none (OSch(!osch_counter, (o,i,s)))

let vwit : (v,t) bndr -> prop -> prop -> valu =
  fun f a b ->
    let valu = (f,a,b) in
    let w =
      try VWitHash.find vwit_hash valu
      with Not_found ->
        let rec refr ?(force=false) w =
          if force || exists_set !(w.vars) then
            begin
              let oldvars = !(w.vars) in
              Timed.(w.vars := VWit.vars valu);
              Timed.(w.hash := VWit.hash valu);
              List.iter (fun (U(_,v)) ->
                  let same (U(_,w)) = v.uvar_key = w.uvar_key in
                  if not (List.exists same oldvars)
                  then uvar_hook v (fun () -> refr w)) !(w.vars);
              VWitHash.add vwit_hash valu w
            end
        in
        let rec w = { vars = ref []
                    ; hash = ref 0
                    ; refr = (fun () -> refr w)
                    ; valu }
        in
        refr ~force:true w;
        VWitHash.add vwit_hash valu w;
        w
    in
    Pos.none (VWit(w))

let swit : (s,t) bndr -> prop -> stac =
  fun f a -> incr swit_counter; Pos.none (SWit(!swit_counter, (f,a)))

let uwit : type a. a sort -> term -> (a,p) bndr -> a ex loc =
  fun s t f -> incr uwit_counter; Pos.none (UWit(!uwit_counter, s, (t,f)))

let ewit : type a. a sort -> term -> (a,p) bndr -> a ex loc =
  fun s t f -> incr ewit_counter; Pos.none (EWit(!ewit_counter, s, (t,f)))
