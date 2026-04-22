open Jasmin
open Jasmin_checksafety
open Utils
open Prog
open Glob_options
open CLI_errors

(* -------------------------------------------------------------------- *)
exception UsageError

let parse () =
  let error () = raise UsageError in
  let infiles = ref [] in
  let set_in s = infiles := s :: !infiles in
  (* Set default option values *)
  if Sys.win32 then set_cc "windows";
  (* Parse command-line arguments *)
  Arg.parse (Arg.align options) set_in usage_msg;
  let c =
    match !color with
    | Auto -> Unix.isatty (Unix.descr_of_out_channel stderr)
    | Always -> true
    | Never -> false
  in
  if c then enable_colors ();
  match !infiles with
  | [] ->
    if !help_intrinsics || !safety_makeconfigdoc <> None || !help_version
    then ""
    else error()
  | [ infile ] ->
    check_options ();
    check_infile infile;
    infile
  | infile :: s :: _ -> raise CLI_errors.(CLIerror (RedundantInputFile (infile, s)))

(* -------------------------------------------------------------------- *)
let check_safety_p pd msf_size asmOp analyze s (p : (_, 'asm) Prog.prog) source_p =
  let () = if SafetyConfig.sc_print_program () then
      let s1,s2 = Glob_options.print_strings s in
      Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                      %a@;@]@."
        s1 s2
        (Printer.pp_prog ~debug:true pd msf_size asmOp) p
  in

  let () = SafetyConfig.pp_current_config_diff () in

  let is_safe =
    List.fold_left (fun res f_decl ->
        if FInfo.is_export f_decl.f_cc then
          let () = Format.eprintf "@[<v>Analyzing function %s@]@."
              f_decl.f_name.fn_name in

          let source_f_decl = List.find (fun source_f_decl ->
              f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
            ) (snd source_p) in
          analyze source_f_decl f_decl p && res
        else res)
      true
      (List.rev (snd p)) in
  if not is_safe then exit(2)

(* -------------------------------------------------------------------- *)
module type ArchWithAnalyze = sig
  module A : Arch_full.Arch
  val analyze :
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) func ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) func ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) prog ->
    bool
end

(** NOTE: cut-copy-pasted out of main. *)
let do_compile
      (type reg regx xreg rflag cond asm_op extra_op)
      (module Arch : Arch_full.Arch
              with type reg = reg
               and type regx = regx
               and type xreg = xreg
               and type rflag = rflag
               and type cond = cond
               and type asm_op = asm_op
               and type extra_op = extra_op)
      visit_prog_after_pass env prog cprog =
  (* TODO: how is [env] in compilation? *)
  match Compile.compile (module Arch) visit_prog_after_pass prog cprog with
  | Utils0.Error e ->
     let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug) e in
     raise (HiError e)
  | Utils0.Ok asm ->
     if !Glob_options.print_export_info_json then begin
         Format.printf "%a" (fun fmt ->
             PrintExportInfo.pp_export_info_json
               fmt
               env
               prog)
           asm
       end;
     if !outfile <> "" then begin
         BatFile.with_file_out !outfile (fun out ->
             let fmt = BatFormat.formatter_of_out_channel out in
             Format.fprintf fmt "%a%!" Arch.pp_asm asm);
         if !debug then Format.eprintf "assembly listing written@."
       end else if List.mem Compiler.Assembly !print_list then
       Format.printf "%a%!" Arch.pp_asm asm
  | exception Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code

(** Convert a Rocq [atype] into an identifier type [int gty].
    NOTE: We use [int] specifically because this is what [var] uses.

    TODO: Does this function already exist?
 *)
let gty_of_atype : Type.atype -> int gty = function
  | Type.Coq_abool -> Bty Bool
  | Type.Coq_aint -> Bty Int
  | Type.Coq_aword ws -> Bty (U ws)
  | Type.Coq_aarr (ws, n) -> Arr (ws, Conv.int_of_pos n)

(** * Oracles: *)

(* FIXME: I need the length of [ret_annot] to match the [f_ret] list
   in the overall function definition.
   I need to modify [oracles]!
   This may need to be parameterized by a list of
   return values, at least the length if I can use dummy
   annotatons.
 *)

(** Dummy [pident] value. *)
let pident_dummy : Annotations.pident =
  Location.{ pl_loc = Location._dummy; pl_desc = "" }

(** Dummy [Annotations.annotation] *)
let dummy_annot : Annotations.annotation =
  (pident_dummy, None)

(** Generate a list of dummy annotations. *)
let mk_annotations (num : int) : Annotations.annotations =
  BatList.make num dummy_annot

(** Generate "dummy" [return_info] based on the number of return vars.
    TODO: is this correct, how I generate list of lists? *)
let mk_return_info (num_rets : Datatypes.nat) : FInfo.return_info =
  FInfo.{ ret_annot = BatList.make (Conv.int_of_nat num_rets) [];
          ret_loc = Location._dummy; }

(** Generate dummy [fun_info] witness: *)
let mk_fun_info (num_rets : Datatypes.nat) : FInfo.t = 
  (Location._dummy , FInfo.f_annot_empty , FInfo.Export , mk_return_info num_rets)

(** Generate function idientifiers *)
let mk_funname (f : string) : Jasmin.Var0.funname =
  CoreIdent.F.mk f

(** Generate variable identifiers.
   TODO: Rocq side needs to supply a type (again), and the [v_kind].
 *)
let mk_ident (x : string) (k : Wsize.v_kind) (t : Type.atype) : Ident.Ident.ident =
  GV.mk x k (gty_of_atype t) Location._dummy []

let main_oracles : Oracles.oracles = {
    Oracles.to_ident = mk_ident;
    Oracles.to_funname = mk_funname;
    Oracles.to_fun_info = mk_fun_info
  }

(** Copy-pasted type argumetns and [module Arch] parameter
    since otherwise it would infer the wrong type argument for [cprog]'s
    ['asm Expr._uprog]'s unification var ['asm].

    [cprog] is a Jasmin program parameterized by orales for
    generating data opaque in Rocq. *)
let bridge
      (type reg regx xreg rflag cond asm_op extra_op)
      (module Arch : Arch_full.Arch
              with type reg = reg
               and type regx = regx
               and type xreg = xreg
               and type rflag = rflag
               and type cond = cond
               and type asm_op = asm_op
               and type extra_op = extra_op)
      (cprog :
         Arch.extended_op Sopn.asmOp ->
         Oracles.oracles ->
         Arch.extended_op Expr._uprog) : unit =

  (* Dummy argument for [do_compile] *)
  let visit_prog_after_pass ~debug s p =
    ignore (debug, s, p) in

  (* "Rocq prog" *)
  let rprog : Arch.extended_op Expr._uprog = cprog Arch.asmOp main_oracles in
  do_compile (module Arch) visit_prog_after_pass Pretyping.Env.empty
    (Conv.prog_of_cuprog rprog) rprog

let main () =

  try
    let infile = parse() in

    let (module P : ArchWithAnalyze) =
      match !target_arch with
      | X86_64 ->
         (module struct
            module C = (val CoreArchFactory.core_arch_x86 ~use_lea:!lea ~use_set0:!set0 !call_conv)
            module A = Arch_full.Arch_from_Core_arch (C)
            module Safety = SafetyMain.Make (Jasmin_checksafety.X86_safety.X86_safety (A))
            let analyze = Safety.analyze ?fmt:None
          end)
      | ARM_M4 ->
         (module struct
            module C = CoreArchFactory.Core_arch_ARM
            module A = Arch_full.Arch_from_Core_arch (C)
            open Jasmin_checksafety
            module Safety = SafetyMain.Make (Jasmin_checksafety.Arm_safety.Arm_safety (A))
            let analyze = Safety.analyze ?fmt:None
          end)
      | RISCV ->
         (module struct
            module C = CoreArchFactory.Core_arch_RISCV
            module A = Arch_full.Arch_from_Core_arch (C)
            open Jasmin_checksafety
            module Safety = SafetyMain.Make (Jasmin_checksafety.Riscv_safety.Riscv_safety (A))
            let analyze = Safety.analyze ?fmt:None
          end)
    in
    let module Arch = P.A in

    if !safety_makeconfigdoc <> None
    then (
      let dir = oget !safety_makeconfigdoc in
      SafetyConfig.mk_config_doc dir;
      exit 0);

    if !help_intrinsics
    then (Help.show_intrinsics Arch.asmOp_sopn (); exit 0);

    if !help_version
    then (Format.printf "%s@." version_string; exit 0);

    let () = if !check_safety then
        match !safety_config with
        | Some conf -> SafetyConfig.load_config conf
        | None -> () in

    (* NOTE: This procedure invokes [Pretyping.tt_program]. *)
    let env, pprog, _ast =
      try Compile.parse_file Arch.arch_info ~idirs:!Glob_options.idirs infile
      with
      | Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
      | Syntax.ParseError (loc, msg) ->
          let msg =
            match msg with
            | None -> "unexpected token" (* default message *)
            | Some msg -> msg
          in
          hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
    in

    if !print_dependencies then begin
      Format.printf "%a"
        (pp_list " " (fun fmt p -> Format.fprintf fmt "%s" (BatPathGen.OfString.to_string p)))
        (List.tl (List.rev (Pretyping.Env.dependencies env)));
      exit 0
    end;

    (* Check if generated assembly labels will generate conflicts*)
    let label_errors = Label_check.get_labels_errors pprog in
    List.iter Label_check.warn_duplicate_label label_errors;

    eprint Compiler.Typing (Printer.pp_pprog ~debug:true Arch.pointer_data Arch.msf_size Arch.asmOp) pprog;

    let prog =
      try Compile.preprocess Arch.pointer_data Arch.msf_size Arch.asmOp pprog
      with Typing.TyError(loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
    in

    let prog =
      if !slice <> []
      then Slicing.slice !slice prog
      else prog
    in

    if to_warn Linter then begin
      let open Linter in
      let (_globs, funcs) = prog in
      let funcs = List.map RDAnalyser.analyse_function funcs in
      let vi_errors = VariableInitialisation.check_prog ([], funcs) in
      let funcs = List.map LivenessAnalyser.analyse_function funcs in
      let dv_errors = DeadVariables.check_prog ([], funcs) in
      let open CompileError in
      vi_errors @ dv_errors
      |> List.filter (fun e -> e.level <= !Glob_options.linting_level)
      |> List.iter (fun error ->
          warning Linter (Location.i_loc0 error.location) "%t" error.to_text
        )
    end;

    (* The source program, before any compilation pass. *)
    let source_prog = prog in

    (* This function is called after each compilation pass.
        - Check program safety (and exit) if the time has come
        - Pretty-print the program
        - Add your own checker here!
    *)
    let visit_prog_after_pass ~debug s p =
      if s = SafetyConfig.sc_comp_pass () && !check_safety then
        check_safety_p
          Arch.pointer_data
          Arch.msf_size
          Arch.asmOp
          P.analyze
          s
          p
          source_prog
        |> fun () -> exit 0
      else
        eprint s (Printer.pp_prog ~debug Arch.pointer_data Arch.msf_size Arch.asmOp) p
    in

    visit_prog_after_pass ~debug:true Compiler.ParamsExpansion prog;

    let prog =
      match !Glob_options.do_auto_spill with
      | None -> prog
      | Some strategy -> AutoSpill.doit strategy prog
    in

    (* Now call the coq compiler.

        NOTE: the [Env.t] [env] is not needed here!
     *)
    let cprog = Conv.cuprog_of_prog prog in

    if !debug then Printf.eprintf "translated to coq \n%!";

    (* Rudy: Check whether to generate source AST in a  Rocq file. *)
    if !rocq_ast_file <> "" then
      (* TODO: if/how should we continue compilation? *)
      (GenRocqAST.gen_rocq_ast ~filename:!rocq_ast_file ~cprog:cprog; exit 0);

    (* Rudy: compile a file defined with a Rocq AST.
       NOTE: need to manually set which program is compiled. *)
    if !bridge_rocq then
      begin
        bridge (module Arch) Main_succ_prog.prog;
        exit 0
      end;

    let to_exec = Pretyping.Env.Exec.get env in
    if to_exec <> [] then begin
        let exec { L.pl_loc = loc ; L.pl_desc = (f, m) } =
          let ii = L.i_loc0 loc, [] in
          try
            let pp_range fmt (ptr, sz) =
              Format.fprintf fmt "%a:%a" Z.pp_print ptr Z.pp_print sz in
            Format.printf "/* Evaluation of %s (@[<h>%a@]):@." f.fn_name
              (pp_list ",@ " pp_range) m;
            let _m, vs =
              (* TODO: allow to configure the initial stack pointer *)
              (match
                 Evaluator.initial_memory Arch.reg_size (Z.of_string "1024") m
               with
               | Utils0.Ok m -> m
               | Utils0.Error err -> raise (Evaluator.Eval_error (ii, err)))
              |> Evaluator.run
                   (module Arch)
                   (Expr.to_uprog Arch.asmOp cprog)
                   ii f []
            in

            Format.printf "@[<v>%a@]@."
              (pp_list "@ " Evaluator.pp_val) vs;
            Format.printf "*/@."
          with Evaluator.Eval_error (ii,err) ->
            let i_loc, _ = ii in
            hierror ~loc:(Lmore i_loc) ~kind:"evaluation error" "%a" Evaluator.pp_error err
        in
        List.iter exec to_exec
      end;

    begin  do_compile (module Arch) visit_prog_after_pass env prog cprog   end
  with


  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1

  | UsageError ->
    Arg.usage (Arg.align options) usage_msg;
    exit 1

  | CLIerror e ->
    Format.eprintf "%a: %s.\n"
      (pp_print_bold_red Format.pp_print_string) "Error"
      (pp_cli_error e);
    exit 1
