open Sorts
open Ast
open Pos

type assoc = LeftAssoc | RightAssoc | NonAssoc
type infix = { name:string
             ; prio:float
             ; asso:assoc
             ; hiho:bool }

let infix_tbl : (string, infix) Hashtbl.t = Hashtbl.create 101

module SMap = Map.Make(String)

type env =
  { global_sorts  : any_sort SMap.t
  ; local_sorts   : any_sort SMap.t
  ; global_exprs  : any_expr SMap.t
  ; local_exprs   : any_expr SMap.t
  ; global_values : value SMap.t
  ; local_values  : value SMap.t
  ; local_infix   : infix SMap.t }

let empty =
  { global_sorts  = SMap.empty
  ; local_sorts   = SMap.empty
  ; global_exprs  = SMap.empty
  ; local_exprs   = SMap.empty
  ; global_values = SMap.empty
  ; local_values  = SMap.empty
  ; local_infix  = SMap.empty }

let env = ref empty

let find_sort : string -> any_sort =
  fun id -> SMap.find id !env.global_sorts

let find_expr : string -> any_expr =
  fun id -> SMap.find id !env.global_exprs

let find_value : string -> value =
  fun id -> SMap.find id !env.global_values

let add_sort : type a. string -> a sort -> unit =
  fun id s ->
    let global_sorts = SMap.add id (Sort s) !env.global_sorts in
    let local_sorts = SMap.add id (Sort s) !env.local_sorts in
    env := {!env with global_sorts; local_sorts}

let add_expr : type a. strloc -> a sort -> a ebox -> unit =
  fun expr_name s expr_box ->
    let expr_def = Bindlib.unbox expr_box in
    let expr_hash = Hash.hash_expr expr_def in
    let ex = Expr(s, {expr_name; expr_def; expr_hash}) in
    let global_exprs = SMap.add expr_name.elt ex !env.global_exprs in
    let local_exprs = SMap.add expr_name.elt ex !env.local_exprs in
    env := {!env with global_exprs; local_exprs}

let add_value : strloc -> term -> prop -> e_valu -> unit =
  fun value_name value_orig value_type value_eval ->
    let value_hash = Hash.hash_expr (Erase.to_valu value_eval) in
    let value_eras = Erase.to_valu value_eval in
    let nv = { value_name; value_type; value_orig
             ; value_eval; value_eras; value_hash}
    in
    let global_values = SMap.add value_name.elt nv !env.global_values in
    let local_values = SMap.add value_name.elt nv !env.local_values in
    env := {!env with global_values; local_values}

let add_infix : string -> infix -> unit =
  fun sym infix ->
    let local_infix = SMap.add sym infix !env.local_infix in
    env := {!env with local_infix}

let parents = ref []

exception Compile

let output_value ch v = Marshal.(to_channel ch v [Closures])
let input_value ch =
  try Marshal.from_channel ch
  (* NOTE End_of_file should happen only when pml is interrupted *)
  (* while saving. *)
  with Failure _ | End_of_file -> raise Compile

let save_file : string -> unit = fun fn ->
  let cfn = Filename.chop_suffix fn ".pml" ^ ".pmi" in
  let ch = open_out cfn in
  let deps =
    match !parents with
    | []   -> assert false
    | _::l -> let deps = List.concat (List.map (!) !parents) in
              parents := l; List.sort_uniq String.compare deps
  in
  (* make sure load_infix sees a closure too, to recompile
     soon enough *)
  output_value ch (fun _ -> ());
  output_value ch (deps:string list);
  output_value ch !env.local_infix;
  output_value ch (!env.local_sorts, !env.local_exprs, !env.local_values);
  close_out ch

(* Obtain the modification time of a file as a float (neg_infinity is return
   when the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime)
  else neg_infinity

(* Test if a file is more recent than another file (or the binary). *)
let more_recent source target =
  mod_time source > mod_time target

let start fn =
  parents := ref [] :: !parents

let find_file : string -> string = fun fn ->
  let add_fn dir = Filename.concat dir fn in
  let ls = fn :: (List.map add_fn Config.path) in
  let rec find ls =
    match ls with
    | []     -> Output.err_msg "File \"%s\" does not exist." fn; exit 1
    | fn::ls -> if Sys.file_exists fn then fn else find ls
  in find ls

let find_module : string list -> string = fun ps ->
  let fn = (String.concat "/" ps) ^ ".pml" in
  find_file fn

let check_deps deps cfn ch =
  if List.exists (fun source ->
         let source = find_file source in
         let dfn = Filename.chop_suffix source ".pml" ^ ".pmi" in
         more_recent source cfn ||
           not (Sys.file_exists dfn) ||
             more_recent dfn cfn) deps
  then
    begin
      close_in ch;
      raise Compile;
    end

let load_infix : string -> unit = fun fn ->
  let cfn = Filename.chop_suffix fn ".pml" ^ ".pmi" in
  if more_recent fn cfn then raise Compile
  else
    let ch = open_in cfn in
    let _ = input_value ch in
    let (deps:string list) = input_value ch in
    check_deps deps cfn ch;
    let infix = input_value ch in
    SMap.iter (Hashtbl.replace infix_tbl) infix;
    close_in ch

let load_file : string -> unit = fun fn ->
  let cfn = Filename.chop_suffix fn ".pml" ^ ".pmi" in
  begin
    match !parents with
    | [] -> ()
    | dep::_ -> dep := fn :: !dep
  end;
  if more_recent fn cfn then
    raise Compile
  else
    let ch = open_in cfn in
    let _ = input_value ch in
    let (deps:string list) = input_value ch in
    check_deps deps cfn ch;
    let _infix = input_value ch in
    begin
      match !parents with
      | [] -> ()
      | dep::_ -> dep := deps @ !dep
    end;
    let (local_sorts, local_exprs, local_values) =
      input_value ch
    in
    close_in ch;
    let global_sorts  = SMap.fold SMap.add local_sorts !env.global_sorts  in
    let global_exprs  = SMap.fold SMap.add local_exprs !env.global_exprs  in
    let global_values = SMap.fold SMap.add local_values !env.global_values in
    env := { !env with global_sorts; global_exprs; global_values }
