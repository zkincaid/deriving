module type Compare =
sig
  type a
  val compare : a -> a -> int
end

module Defaults (E : Compare) : Compare with type a = E.a

module Compare_immutable (S : sig type a end) : Compare with type a = S.a
module Compare_mutable (S : sig type a end) : Compare with type a = S.a

module Compare_alpha(S : sig type a end) : Compare with type a = S.a
module Compare_int            : Compare with type a = int
module Compare_bool           : Compare with type a = bool
module Compare_float          : Compare with type a = float
module Compare_unit           : Compare with type a = unit
module Compare_char           : Compare with type a = char
module Compare_int32          : Compare with type a = int32
module Compare_int64          : Compare with type a = int64
module Compare_nativeint      : Compare with type a = nativeint

module Compare_string         : Compare with type a = string
module Compare_ref (E : Compare)   : Compare with type a = E.a ref
module Compare_array (E : Compare) : Compare with type a = E.a array
module Compare_list (E : Compare)  : Compare with type a = E.a list
module Compare_option (E : Compare): Compare with type a = E.a option
module Compare_map_s_t (E : Compare) (M : Map.S) : Compare with type a = E.a M.t
