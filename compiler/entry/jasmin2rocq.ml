open Jasmin
open Cmdliner
open CommonCLI
open Utils

(* -------------------------------------------------------------------- *)

let ensure_output_writable path =
  let existed = Sys.file_exists path in
  try
    let oc = open_out_gen [ Open_wronly; Open_creat; Open_append ] 0o666 path in
    close_out oc;
    if not existed then BatPervasives.ignore_exceptions Sys.remove path
  with Sys_error msg ->
    hierror ~loc:Lnone ~kind:"I/O error" "cannot write output file %S (%s)" path
      msg

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract output pass slice split file program_name warn =
    if not warn then nowarning ();
    Option.may ensure_output_writable output;
    let prog = parse_and_compile (module A) ~wi2i:false pass file idirs in
    let prog = if slice = [] then prog else Slicing.slice slice prog in
    if split then
      match output with
      | None ->
          Format.eprintf "--split requires -o to specify an output file@.";
          exit 1
      | Some f ->
          ToRocq.extract_split arch A.pp_extended_op_for_rocq prog program_name f
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
        ToRocq.extract arch A.pp_extended_op_for_rocq prog program_name fmt;
        Format.pp_print_flush fmt ();
        close ()
      with e ->
        BatPervasives.ignore_exceptions close ();
        raise e
  in
  fun output pass slice split file program_name warn ->
    match extract output pass slice split file program_name warn with
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

let program_name =
  let doc = "Name of the generated Rocq program definition." in
  Arg.(required & pos 1 (some string) None & info [] ~docv:"PROGRAM" ~doc)

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
      $ slice $ split $ file $ program_name $ warn)
  |> Cmd.eval |> exit
