
(* Le petit programme suivant chronomètre le temps nécessaire pour
appliquer une fonction à un argument (le temps de calcul de l'argument
n'étant pas compris). *)

(* necessite la librairie UNIX *)

let chrono s f x =
  let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
  try
    let r = f x in
    let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
    Printf.printf "%s: %.2fs ... " s ((ut' -. ut) +. (st' -. st));
    flush stdout;
    r
  with e ->
    let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
    Printf.printf "%s: %.2fs ... " s ((ut' -. ut) +. (st' -. st));
    flush stdout;
    raise e

let all_chronos = ref []

let create_chrono (name:string) =
  let chrono = ref (name, false, 0.0, 0) in
  all_chronos:=chrono::!all_chronos;
  chrono

let save_chronos () =
  List.map (fun chr -> let (name, _ , _, _) as r = !chr in
                       chr := name, false, 0.0, 0; r) !all_chronos

let restore_chronos backup =
  List.iter2 (fun chr saved -> chr:=saved) !all_chronos backup

let chrono_stack = ref (0.0, 0.0)

let pop_time ud0 sd0 ut st =
  let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
  let (ud1, sd1) = !chrono_stack in
  let ud = ut' -. ut +. ud0 and sd = st' -. st +. sd0 in
  chrono_stack := (ud, sd);
  (ud -. ud1) +. (sd -. sd1)

let cumulative_chrono p f x =
  let name, active, cur, count = !p in
  if active then f x else begin
    p:= name, true, cur, count+1;
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    let (ud0, sd0) = !chrono_stack in
    let ut = ut and st = st in
    try
      let r = f x in
      let t = pop_time ud0 sd0 ut st in
      let _, _, cur, count = !p in
      p := (name, false, cur +. t, count);
      r
    with e ->
      let t = pop_time ud0 sd0 ut st in
      let _, _, cur, count = !p in
      p := (name, false, cur +. t, count);
      raise e
  end

let cumulative_chrono2 p f x1 x2 =
  cumulative_chrono p (f x1) x2

let cumulative_chrono3 p f x1 x2 x3 =
  cumulative_chrono p (f x1 x2) x3

let cumulative_chrono4 p f x1 x2 x3 x4 =
  cumulative_chrono p (f x1 x2 x3) x4

let get_time p =
  let active, cur, count = !p in cur

let get_count p =
  let active, cur, count = !p in count

let display_all () =
  List.iter (fun c ->
      let (name, _, cur, count) = !c in
      Printf.eprintf "%s: %f %d\n" name cur count) !all_chronos
