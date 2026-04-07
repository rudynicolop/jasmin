
(** Generate a Rocq file with the source program's AST. *)

let print_rocq_record ~fmt:(fmt : Format.formatter) (data : (string * string) list) =
  Format.fprintf fmt "{|@.";
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@.")
    begin fun fmt (field_name, field_content) ->
    Format.fprintf fmt "%s := %s" field_name field_content
    end
    fmt data;
  Format.fprintf fmt "|}@."

let print_func ~fmt:(fmt : Format.formatter) (func : ('asm, 'extra_fun_t) Expr._fun_decl) =
  let fname = fst func in
  let fdef = snd func in
  Format.fprintf fmt "Definition %s := @." fname.fn_name;
  (* TODO: need to properly print stuff *)
  ignore fdef;
  (* TODO: should I use record constructor syntax or should I invoke [MkFun]? *)
  print_rocq_record ~fmt:fmt [
      "f_info", "FunInfo.witness";
      (* TODO: what is [f_contract]? *)
      "f_contract", "None";
      "f_typin", "[]";
      "f_params", "[]";
      "f_body", "[]";
      "f_typout", "[]";
      "f_res", "[]";
      (* TODO: how do I ignore the [f_extra]? *)
      "f_extra", "tt";
    ];
  Format.fprintf fmt ".@."

(** Print program. *)
let print_program ~fmt:(fmt : Format.formatter) ~cprog:(cprog : 'asm Expr._uprog) =
  List.iter (print_func ~fmt:fmt) cprog.p_funcs

(** Print imports/exports. *)
let print_imports ~fmt:(fmt : Format.formatter) =
   Format.pp_print_list 
     ~pp_sep:(fun fmt () -> Format.fprintf fmt ".@.")
     begin fun fmt module_name ->
     Format.fprintf fmt "Require Export %s" module_name
     end
     fmt ["Jasmin.expr"];
   (* Add trailing period separator. *)
   Format.fprintf fmt ".@."

(** Print section context variables.

    This procedure is responsible for populating the generated ".v" file
    with contextual axioms to obtain opaque data types.

    Thus this procedure declares:
    - TODO:
 *)
let print_context ~fmt:(fmt : Format.formatter) =
  Format.fprintf fmt "Context@.";
  Format.fprintf fmt ".@."

(** Generate Rocq file contents with sections. *)
let gen_contents ~fmt:(fmt : Format.formatter) ~cprog:(cprog : 'asm Expr._uprog) =
  print_imports ~fmt:fmt;
  let section_name = "prog" in
  Format.fprintf fmt "Section %s.@." section_name;
  print_program ~fmt:fmt ~cprog:cprog;
  Format.fprintf fmt "End %s.@." section_name

(** Entry point to generate Rocq file.
    Requires:
    - [`asm] is a type parameter for the assembly operations.
    - [filename] is a client-provided name for the Rocq file to generate.
    - [cprog] is the Rocq-extracted AST of the source Jasmin program.
 *)
let gen_rocq_ast ~filename:(filename : string) ~cprog:(cprog : 'asm Expr._uprog) =
  let rocq_filename = Format.sprintf "%s.v" filename in
  BatFile.with_file_out rocq_filename
    begin
    fun out ->
      let fmt = BatFormat.formatter_of_out_channel out in
      gen_contents ~fmt:fmt ~cprog:cprog
    end
