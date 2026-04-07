
(** Generate a Rocq file with the source program's AST. *)

(** Generate Rocq file with sections. *)
let gen_file ~fmt:(fmt : Format.formatter) ~cprog:(cprog : 'asm Expr._uprog) =
  let section_name = "prog" in
  Format.fprintf fmt "Section %s.@." section_name;
  (* TODO: print cprog *)
  ignore cprog;
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
      gen_file ~fmt:fmt ~cprog:cprog
    end
