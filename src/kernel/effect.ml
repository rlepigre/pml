(** This module implements the effect decoration for arrow types *)

(** Second time for uvar and effect. We need two level of time because
backtracking in the pool should not backtrack unification variables that we
have in Ast and in this module.

The level Timed.Time corresponds to change in the branch of the proof,
which require some rollback on pointers value in the pool.

The level UTimed corresponds to real backtracking in the proof search.
*)
module UTimed = Timed.Make(Timed.Time)

open Output
let log_eff = Log.register 'z' (Some "eff") "effect computation"
let log_eff = Log.(log_eff.p)

type pml_effect =
  Loop | CallCC

module Effect = struct
  type t = pml_effect
  let all = [ Loop; CallCC ]
  let print ch = function
    | Loop   -> Printf.fprintf ch "Loop"
    | CallCC -> Printf.fprintf ch "CallCC"
end

include Finset.Make(UTimed)(Effect)

let cvg = known [CallCC]

let print = Effect.print
