val rocq_sanitize_s : string -> string

val pp_rocq_option :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

val pp_wsize : Format.formatter -> Wsize.wsize -> unit
val pp_bare : Format.formatter -> string -> unit
val pp_with_ws : Format.formatter -> string -> Wsize.wsize -> unit

val pp_with_ws2 :
  Format.formatter -> string -> Wsize.wsize * Wsize.wsize -> unit

val pp_ve : Format.formatter -> string -> Wsize.velem -> unit
val pp_ve_ws : Format.formatter -> string -> Wsize.velem * Wsize.wsize -> unit

val pp_ve_ws_ve_ws :
  Format.formatter ->
  string ->
  Wsize.velem * Wsize.wsize * Wsize.velem * Wsize.wsize ->
  unit

val pp_rk_ws :
  Format.formatter -> string -> Wsize.reg_kind * Wsize.wsize -> unit

val pp_s_ws :
  Format.formatter -> string -> Wsize.signedness * Wsize.wsize -> unit

val extract :
  Utils.architecture ->
  (Format.formatter ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op ->
  unit) ->
  ( 'info,
    ( 'reg,
      'regx,
      'xreg,
      'rflag,
      'cond,
      'asm_op,
      'extra_op )
    Arch_extra.extended_op )
  Prog.prog ->
  string ->
  Format.formatter ->
  unit

val extract_split :
  Utils.architecture ->
  (Format.formatter ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op ->
  unit) ->
  ( 'info,
    ( 'reg,
      'regx,
      'xreg,
      'rflag,
      'cond,
      'asm_op,
      'extra_op )
    Arch_extra.extended_op )
  Prog.prog ->
  string ->
  string ->
  unit
