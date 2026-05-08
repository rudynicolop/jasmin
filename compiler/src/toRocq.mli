val pp_opt :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  'a option ->
  unit

val pp_ws :
  string ->
  Format.formatter ->
  Wsize.wsize ->
  unit

val extract :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  string ->
  _ Prog.prog ->
  unit
