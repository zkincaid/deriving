open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Compare"
  let runtimename = "Deriving_Compare"
  let default_module = None
  let alpha = Some "Compare_alpha"
  let allow_private = true
  let predefs = [
    ["unit"], ["Deriving_Compare";"unit"];
    ["bool"], ["Deriving_Compare";"bool"];
    ["char"], ["Deriving_Compare";"char"];
    ["int"], ["Deriving_Compare";"int"];
    ["int32"], ["Deriving_Compare";"int32"];
    ["Int32";"t"], ["Deriving_Compare";"int32"];
    ["int64"], ["Deriving_Compare";"int64"];
    ["Int64";"t"], ["Deriving_Compare";"int64"];
    ["nativeint"], ["Deriving_Compare";"nativeint"];
    ["float"], ["Deriving_Compare";"float"];
    ["num"], ["Deriving_num";"num"];
    ["list"], ["Deriving_Compare";"list"];
    ["option"], ["Deriving_Compare";"option"];
    ["string"], ["Deriving_Compare";"string"];
    ["ref"], ["Deriving_Compare";"ref"];
    ["array"], ["Deriving_Compare";"array"];
  ]
  let depends = []
end

module Builder(Generator : Defs.Generator) = struct

  open Generator.Loc
  open Camlp4.PreCast
  open Description

  module Helpers = Generator.AstHelpers

  let and_guard x y = match x, y with
    | <:expr< >>, e | e, <:expr< >> -> e
    | x, y -> <:expr< $x$ && $y$ >>

  (* Last two cases can never be matched *)
  let rec drop_unused = function
    | [] -> assert false
    | [x;y] -> []
    | (x::xs) -> x::(drop_unused xs)

  let lprefix = "l" and rprefix = "r"

  let wrap cases =
    [ <:str_item< let compare l r = match l, r with $list:cases$ >>]

  let generator = (object (self)

    method proxy () =
      None, [ <:ident< compare >>; ]

    inherit Generator.generator

    method tuple ctxt tys =
      let n = List.length tys in
      let lnames, lpatt, _ = Helpers.tuple ~param:lprefix n in
      let rnames, rpatt, _ = Helpers.tuple ~param:rprefix n in
      let lex_compare ty (lid, rid) e =
	<:expr< 
	  match $self#call_expr ctxt ty "compare"$ $lid:lid$ $lid:rid$ with
	  | 0   -> $e$
	  | cmp -> cmp
        >>
      in
      let expr =
        List.fold_right2 lex_compare tys (List.zip lnames rnames) <:expr< 0 >>
      in
      wrap [ <:match_case< (($lpatt$),($rpatt$)) -> $expr$ >> ]

    method case ctxt (name,args) =
      match args with
      | [] ->
	[ <:match_case< ($uid:name$, $uid:name$) -> 0 >>;
	  <:match_case< ($uid:name$, _) -> 1 >>;
	  <:match_case< (_, $uid:name$) -> -1 >> ]
      | _ ->
          let nargs = List.length args in
          let _, lpatt, lexpr = Helpers.tuple ~param:lprefix nargs
          and _, rpatt, rexpr = Helpers.tuple ~param:rprefix nargs in
	  [ <:match_case< ($uid:name$ $lpatt$, $uid:name$ $rpatt$) ->
  	      $self#call_expr ctxt (`Tuple args) "compare"$ $lexpr$ $rexpr$ >>;
	    <:match_case< ($uid:name$ _, _) -> 1 >>;
	    <:match_case< (_, $uid:name$ _) -> -1 >> ]

    method sum ?eq ctxt tname params constraints summands =
      wrap (drop_unused (List.concat_map (self#case ctxt) summands))


    method field ctxt (name, ty, mut) =
      assert(mut <> `Mutable);
      <:expr< $self#call_poly_expr ctxt ty "compare"$ $lid:lprefix ^ name$ $lid:rprefix ^ name$ >>

    method record ?eq ctxt tname params constraints fields =
      if List.exists (function (_,_,`Mutable) -> true | _ -> false) fields then
	raise (Base.Underivable
		 (classname ^ " cannot be derived for the type "
		  ^ tname ^" because it contains a mutable field"))
      else 
	let lpatt = Helpers.record_pattern ~prefix:lprefix fields in
	let rpatt = Helpers.record_pattern ~prefix:rprefix fields in
	let lex_compare f e =
	  <:expr< 
	    match $self#field ctxt f$ with
	    | 0   -> $e$
	    | cmp -> cmp
          >>
	in
	let expr = List.fold_right lex_compare fields <:expr< 0 >> in
	wrap [ <:match_case< (($lpatt$), ($rpatt$)) -> $expr$ >> ]

    method polycase ctxt : Pa_deriving_common.Type.tagspec -> Ast.match_case list = function
      | Type.Tag (name, []) ->
	[ <:match_case< (`$name$, `$name$) -> 0 >>;
          <:match_case< (`$name$, _) -> 1 >>;
          <:match_case< (_, `$name$) -> -1 >> ]
      | Type.Tag (name, es) ->
	[ <:match_case< `$name$ l, `$name$ r -> $self#call_expr ctxt (`Tuple es) "compare"$ l r >>;
	  <:match_case< `$name$ _, _ -> 1 >>;
	  <:match_case< _, `$name$ _ -> -1 >> ]
      | Type.Extends t ->
          let lpatt, lguard, lcast = Generator.cast_pattern ctxt ~param:"l" t in
          let rpatt, rguard, rcast = Generator.cast_pattern ctxt ~param:"r" t in
          [ <:match_case<
              ($lpatt$, $rpatt$) when $and_guard lguard rguard$ ->
                $self#call_expr ctxt t "compare"$ $lcast$ $rcast$ >>;
              <:match_case< ($lpatt$, _) when $lguard$ -> 1 >>;
              <:match_case< (_, $rpatt$) when $rguard$ -> -1 >> ]

    method variant ctxt tname params constraints (spec, tags) =
      wrap (drop_unused (List.concat_map (self#polycase ctxt) tags))

  end :> Generator.generator)

  let classname = Description.classname
  let runtimename = Description.runtimename
  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator
  let generate_expr = Generator.generate_expr generator

end

include Base.RegisterFullClass(Description)(Builder)
