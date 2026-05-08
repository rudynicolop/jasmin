open Jasmin
open Common

let path = "success"

let load_and_print n name =
  Format.printf "File %s: " name;
  let p = load_file (Filename.concat path name) in
  let out_name = Filename.remove_extension name ^ ".v" in
  Format.eprintf "cwd=%s out=%s@." (Sys.getcwd ()) out_name;
  let oc = open_out out_name in
  let fmt = Format.formatter_of_out_channel oc in
  match
    ToRocq.extract ~imports:false ~split:false
      Utils.X86_64 Arch.reg_size Arch.msf_size Arch.asmOp
      Arch.pp_extended_op_for_rocq p "p" fmt
  with
  | () ->
      Format.pp_print_flush fmt ();
      close_out oc;
      (*Sys.remove out_name;*)
      Format.printf "OK@.";
      n
  | exception e ->
      close_out_noerr oc;
      (try Sys.remove out_name with _ -> ());
      Format.eprintf "Extraction failed: %s@." (Printexc.to_string e);
      n + 1

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.fold_left load_and_print 0 cases |> exit
