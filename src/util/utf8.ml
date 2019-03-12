let next s pos =
  let cc = Char.code s.[pos] in
  if cc lsr 7 = 0 then pos + 1 else
  if (cc lsr 6) land 1 = 0 then invalid_arg "utf8_next" else
  if (cc lsr 5) land 1 = 0 then pos + 2 else
  if (cc lsr 4) land 1 = 0 then pos + 3 else
  if (cc lsr 3) land 1 = 0 then pos + 4 else
  invalid_arg "Utf8.next"

let len s =
  let len = String.length s in
  let pos = ref 0 in
  let res = ref 0 in
  while !pos < len do
    pos := next s !pos;
    incr res
  done; !res

let sub s start len =
  let slen = String.length s in
  let rec find pos num =
    if num < 0 then invalid_arg "Utf8.sub (negative index)";
    if num = 0 then pos else
      begin
        if pos >= slen then invalid_arg "Utf8.sub (char out of bound)";
        find (next s pos) (num-1)
      end
  in
  let start = find 0 start in
  let len   = (find start len) - start in
  String.sub s start len
