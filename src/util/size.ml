(* Code instrumentation (rough size of expression). *)
let binary_size : type a. a -> int = fun e ->
  let open Marshal in
  String.length (to_string e [Closures])
