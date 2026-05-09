open Jasmin
open Cmdliner
open CommonCLI
open Utils
open Prog

(* -------------------------------------------------------------------- *)
(* Slicing: keep only selected functions and their transitive callees *)
(* TODO Doesn't Slicing.slice work? *)

let callees_of_func fd =
  let rec from_stmt acc c = List.fold_left from_instr acc c
  and from_instr acc i =
    match i.i_desc with
    | Ccall (_, fn, _) -> Ss.add fn.fn_name acc
    | Cif (_, c1, c2) -> from_stmt (from_stmt acc c1) c2
    | Cfor (_, _, c) -> from_stmt acc c
    | Cwhile (_, c1, _, _, c2) -> from_stmt (from_stmt acc c1) c2
    | _ -> acc
  in
  from_stmt Ss.empty fd.f_body

let slice_prog (gd, funcs) names =
  (* Build a map from function name to func *)
  let by_name =
    List.fold_left (fun m fd -> Ms.add fd.f_name.fn_name fd m) Ms.empty funcs
  in
  (* Compute transitive closure of callees *)
  let rec close todo seen =
    if Ss.is_empty todo then seen
    else
      let name = Ss.choose todo in
      let todo = Ss.remove name todo in
      if Ss.mem name seen then close todo seen
      else
        let seen = Ss.add name seen in
        let todo =
          match Ms.find_opt name by_name with
          | Some fd -> Ss.union todo (callees_of_func fd)
          | None -> todo
        in
        close todo seen
  in
  let keep = close (Ss.of_list names) Ss.empty in
  let funcs = List.filter (fun fd -> Ss.mem fd.f_name.fn_name keep) funcs in
  (gd, funcs)

(* -------------------------------------------------------------------- *)

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract output pass slice imports file warn =
    if not warn then nowarning ();
    let prog = parse_and_compile (module A) ~wi2i:false pass file idirs in
    let prog = match slice with [] -> prog | names -> slice_prog prog names in
    let fmt, close =
      match output with
      | None -> (Format.std_formatter, fun () -> ())
      | Some f ->
          let out = open_out f in
          let fmt = Format.formatter_of_out_channel out in
          (fmt, fun () -> close_out out)
    in
    try
      ToRocq.extract ~imports arch A.reg_size A.msf_size A.asmOp
        A.pp_extended_op_for_rocq prog "p" fmt;
      Format.pp_print_flush fmt ();
      close ()
    with e ->
      BatPervasives.ignore_exceptions (fun () -> close ()) ();
      raise e
  in
  fun output pass slice imports file warn ->
    match extract output pass slice imports file warn with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let after_pass =
  let alts =
    List.map
      (fun s -> (fst (Glob_options.print_strings s), s))
      Compiler.(List.filter (( > ) StackAllocation) compiler_step_list)
  in
  let doc =
    Format.asprintf
      "Run after the given compilation pass. Only passes before stack \
       allocation are supported, since later passes produce a different \
       program representation. Possible values are %s."
      (Arg.doc_alts_enum alts)
  in
  let passes = Arg.enum alts in
  Arg.(value & opt passes ParamsExpansion & info [ "compile"; "after" ] ~doc)

let imports =
  let doc = "Print Rocq imports and axioms at the top of the output." in
  Arg.(value & flag & info [ "imports" ] ~doc)

let slice =
  let doc =
    "Only extract the given function (and its dependencies). This argument may \
     be repeated to extract many functions. If not given, all functions will \
     be extracted."
  in
  Arg.(value & opt_all string [] & info [ "slice"; "only"; "on" ] ~doc)

let file =
  let doc = "The Jasmin source file to extract" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let () =
  let doc = "Extract Jasmin program to Rocq representation" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin2rocq" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_extract $ arch $ call_conv $ idirs $ output $ after_pass
      $ slice $ imports $ file $ warn)
  |> Cmd.eval |> exit
