let get_lines : string -> int -> int -> string list = fun fname off1 off2 ->
  let ch = open_in fname in
  for i = 1 to off1 - 1 do ignore (input_line ch) done;
  let lines = ref [] in
  begin
    try
      for i = max 1 off1 to off2 do
        lines := input_line ch :: !lines
      done
    with End_of_file -> ()
  end;
  close_in ch;
  List.rev !lines


type config =
  { leading  : int
  ; trailing : int
  ; numbers  : bool
  ; prefix   : string }

let default_config =
  { leading  = 2
  ; trailing = 2
  ; numbers  = true
  ; prefix   = "" }


let separator : string = String.make 78 '='

let header : string -> string = fun s ->
  "== " ^ s ^ " " ^ (String.make (74 - String.length s) '=')

let red : string -> string =
  fun s -> "\027[31m" ^ s ^ "\027[0m"

let ulined : string -> string =
  fun s -> "\027[4m" ^ s ^ "\027[0m"

exception Quote_error of Pos.pos * string
let quote_error : type a. Pos.pos -> string -> a = fun pos msg ->
  raise (Quote_error(pos, msg))

let quote_file : ?config:config -> out_channel -> Pos.pos -> unit =
  fun ?(config=default_config) oc pos ->
    let open Pos in
    match pos.fname with
    | None       -> quote_error pos "Unable to quote (no filename)"
    | Some fname ->
        if pos.start_line > pos.end_line then
          quote_error pos "Invalid line position (start after end)";
        let off1 = max 1 (pos.start_line - config.leading)  in
        let off2 = pos.end_line   + config.trailing in
        let lines =
          try get_lines fname off1 off2 with _ ->
            quote_error pos "Cannot obtain the lines from the file"
        in
        let max_num = String.length (string_of_int off2) in
        let print_i i line =
          let num = i + off1 in
          let in_pos = pos.start_line <= num && num <= pos.end_line in
          let number =
            if config.numbers then
              let num = string_of_int num in
              let pad = String.make (max_num - String.length num) ' ' in
              pad ^ (if in_pos then red num else num) ^ "|"
            else ""
          in
          let line =
            let len = Utf8.len line in
            if not in_pos then line else
            if num = pos.start_line && num = pos.end_line then
              let n = pos.end_col - pos.start_col + 1 in
              if pos.end_col < pos.start_col then
                begin
                  Printf.eprintf ">>> pos.start_col   = %i\n" pos.start_col;
                  Printf.eprintf ">>> pos.end_col     = %i\n" pos.end_col;
                  quote_error pos "Invalid column position (start after end)";
                end;
              let l = Utf8.sub line 0 (pos.start_col-1) in
              let c = Utf8.sub line (pos.start_col-1) n in
              let r = Utf8.sub line pos.end_col (len - pos.end_col) in
              l ^ ulined (red c) ^ r
            else if num = pos.start_line then
              let n = pos.start_col - 1 in
              let l = Utf8.sub line 0 n in
              let r = Utf8.sub line n (len - n) in
              l ^ ulined (red r)
            else if num = pos.end_line then
              let n = pos.end_col in
              let l = Utf8.sub line 0 n in
              let r = Utf8.sub line n (len - n) in
              ulined (red l) ^ r
            else ulined (red line)
          in
          Printf.fprintf oc "%s%s%s\n" config.prefix number line
        in
        Printf.fprintf oc "%s%s\n" config.prefix (header fname);
        List.iteri print_i lines;
        Printf.fprintf oc "%s%s\n" config.prefix separator
