(*pp camlp4of *)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Defs

module Description : ClassDescription = struct
  type t
  let classname = "Bounded"
  let default_module = None
  let allow_private = false
end

module InContext (L : Loc) : Class = struct

  open Base
  open Utils
  open Type
  open Camlp4.PreCast

  open L
  module Helpers = Base.InContext(L)(Description)
  open Helpers

  let wrap min max =
    [ <:str_item< let min_bound = $min$ >>; <:str_item< let max_bound = $max$ >> ]

  let instance = object (self)
    inherit make_module_expr

    method tuple ctxt ts = 
    let minBounds, maxBounds = 
      List.split (List.map
                    (fun t -> let e = self#expr ctxt t in 
                       <:expr< let module M = $e$ in M.min_bound >>,
                       <:expr< let module M = $e$ in M.max_bound >>) ts) in
    wrap (tuple_expr minBounds) (tuple_expr maxBounds)

    method sum ?eq ctxt ((tname,_,_,_,_) as decl) summands = 
    let names = ListLabels.map summands
        ~f:(function
              | (name,[]) -> name
              | (name,_) -> raise (Underivable ("Bounded cannot be derived for the type "^
                                                  tname ^" because the constructor "^
                                                  name^" is not nullary"))) in
        wrap <:expr< $uid:List.hd names$ >> <:expr< $uid:List.last names$ >>

    method variant ctxt decl (_, tags) = 
    let names = ListLabels.map tags
        ~f:(function
              | Tag (name, None) -> name
             | Tag (name, _) -> raise (Underivable ("Bounded cannot be derived because the tag "^
                                                      name^" is not nullary"))
             | _ -> raise (Underivable ("Bounded cannot be derived for this "
                                        ^"polymorphic variant type"))) in
      wrap <:expr< `$List.hd names$ >> <:expr< `$List.last names$ >>

  (* should perhaps implement this one *)
  method record ?eq _ (tname,_,_,_,_) = raise (Underivable ("Bounded cannot be derived for record types (i.e. "^
                                                     tname^")"))
  end

  let make_module_expr = instance#rhs
  let generate = default_generate ~make_module_expr ~make_module_type
  let generate_sigs = default_generate_sigs ~make_module_sig

end

module Bounded = Base.Register(Description)(InContext)
