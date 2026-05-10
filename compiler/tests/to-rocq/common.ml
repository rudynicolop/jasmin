open Jasmin

module Make (C : Arch_full.Core_arch) = struct
  module Arch = Arch_full.Arch_from_Core_arch (C)

  let load_file name =
    let open Pretyping in
    match
      name
      |> tt_file Arch.arch_info Env.empty None None
      |> fst |> Env.decls
      |> Compile.preprocess Arch.pointer_data Arch.msf_size Arch.asmOp
      |> Compile.do_spill_unspill Arch.asmOp
    with
    | exception TyError (loc, e) ->
        Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
        assert false
    | exception Syntax.ParseError (loc, None) ->
        Format.eprintf "Parse error: %a@." Location.pp_loc loc;
        assert false
    | Error msg ->
        Format.eprintf "%a@." Utils.pp_hierror msg;
        assert false
    | Ok p -> p
end
