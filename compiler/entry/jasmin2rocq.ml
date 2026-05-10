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
  let extract output pass slice ids split file warn =
    if not warn then nowarning ();
    let prog = parse_and_compile (module A) ~wi2i:false pass file idirs in
    let prog = match slice with [] -> prog | names -> slice_prog prog names in
    if split then
      match output with
      | None ->
          Format.eprintf "--split requires -o to specify an output file@.";
          exit 1
      | Some f ->
          ToRocq.extract_split ~ids arch A.pp_extended_op_for_rocq prog "p" f
    else
      let fmt, close =
        match output with
        | None -> (Format.std_formatter, fun () -> ())
        | Some f ->
            let out = open_out f in
            let fmt = Format.formatter_of_out_channel out in
            (fmt, fun () -> close_out out)
      in
      try
        ToRocq.extract ~ids arch A.pp_extended_op_for_rocq prog "p" fmt;
        Format.pp_print_flush fmt ();
        close ()
      with e ->
        BatPervasives.ignore_exceptions (fun () -> close ()) ();
        raise e
  in
  fun output pass slice ids split file warn ->
    match extract output pass slice ids split file warn with
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

let ids =
  let doc =
    "Print variable and function names without appending their internal unique \
     identifier. This may cause name clashes with other definitions (for \
     example, if two local variables from different functions share the same \
     name)."
  in
  Arg.(value & vflag true [ (false, info [ "no-ids" ] ~doc) ])

let split =
  let doc =
    "Write globals, function names, each function, and the program to separate \
     files. Requires -o $(i,OUTPUT FILE). All files are created in the \
     directory of $(i,OUTPUT FILE). If $(i,BASE) is the basename of $(i,OUTPUT \
     FILE) (without extension), the printer generates: (1) $(i,OUTPUT FILE) \
     for the program, (2) $(i,BASE)_globs.v for globals, (3) \
     $(i,BASE)_funnames.v for function names, (4) $(i,BASE)_<funname>.v for \
     each function <funname>, and (5) $(i,_CoqProject), and (6) $(i,Makefile). \
     The _CoqProject file assumes that it is in a directory at the top level \
     of the Jasmin repository. To use other locations, replace the first\n\
    \      argument to each -R command."
  in
  Arg.(value & flag & info [ "split" ] ~doc)

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
      `S "NAMING";
      `P
        "All generated names are sanitized (every non-letter and non-number \
         symbol is replaced with an underscore), which may cause clashes.";
      `P
        "The printer derives additional names from base names as follows: (1) \
         a variable $(i,v) produces two definitions: $(i,v) and $(i,v_data); \
         (2) a function $(i,f) produces seven definitions: $(i,f), \
         $(i,tyin_f), $(i,args_f), $(i,tyout_f), $(i,res_f), $(i,body_f), and \
         $(i,fd_f); (3) the program name $(i,p) produces two definitions: \
         $(i,p_gds) and $(i,p).";
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
      $ slice $ ids $ split $ file $ warn)
  |> Cmd.eval |> exit
