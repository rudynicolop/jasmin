val rocq_sanitize_s : string -> string

val pp_rocq_option :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

val pp_wsize : Format.formatter -> Wsize.wsize -> unit
val pp_bare : string -> Format.formatter -> unit
val pp_with_ws : string -> Format.formatter -> Wsize.wsize -> unit

val pp_with_ws2 :
  string -> Format.formatter -> Wsize.wsize * Wsize.wsize -> unit

val pp_ve : string -> Format.formatter -> Wsize.velem -> unit
val pp_ve_ws : string -> Format.formatter -> Wsize.velem * Wsize.wsize -> unit

val pp_ve_ws_ve_ws :
  string ->
  Format.formatter ->
  Wsize.velem * Wsize.wsize * Wsize.velem * Wsize.wsize ->
  unit

val pp_rk_ws :
  string -> Format.formatter -> Wsize.reg_kind * Wsize.wsize -> unit

val pp_s_ws :
  string -> Format.formatter -> Wsize.signedness * Wsize.wsize -> unit

val extract :
  ?imports:bool ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Sopn.asmOp ->
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
