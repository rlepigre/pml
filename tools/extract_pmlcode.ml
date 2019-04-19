
let input = Sys.argv.(1)

let output = Sys.argv.(2)

let chin = open_in input

let chout = open_out output

let occur s1 s2 =
  let open Str in
  let r = regexp_string s1 in
  try
    ignore (search_forward r s2 0);
    true
  with
    Not_found -> false

let min_space = ref max_int
let lines = ref []

let count_space s =
  let len = String.length s in
  let rec fn i =
    if i < len && s.[i] = ' ' then fn (i+1)
    else if i >= len then ()
    else min_space := min !min_space i
  in
  fn 0

let remove_space s =
  let len = String.length s in
  if len > !min_space then
    String.sub s !min_space (len - !min_space)
  else
    ""

let _ =
  try
    while true do
      let line = input_line chin in
      if occur "\\begin{pmlcode}" line then
        try
          while true do
            let line = input_line chin in
            if occur "\\end{pmlcode}" line then raise Exit;
            count_space line;
            lines := line :: !lines
          done
        with Exit -> lines := "" :: !lines
    done
  with End_of_file ->
    Printf.printf "%d\n%!" !min_space;
    List.iter (fun line ->
        let line = remove_space line in
        output_string chout line;
        output_char chout '\n') (List.rev !lines)

let _ = close_out chout
let _ = close_in  chin
