open Jasmin
open Common

let path = "success"

let find_proofs_dir () =
  let rec walk dir =
    let cand = Filename.concat dir "proofs" in
    if
      Sys.file_exists cand && Sys.is_directory cand
      && Sys.file_exists (Filename.concat cand "_CoqProject")
    then cand
    else
      let parent = Filename.dirname dir in
      if parent = dir then begin
        prerr_endline
          "Could not locate Jasmin proofs/ directory; set JASMIN_PROOFS_DIR.";
        exit 2
      end
      else walk parent
  in
  walk (Sys.getcwd ())

let proofs_dir =
  match Sys.getenv_opt "JASMIN_PROOFS_DIR" with
  | Some d -> d
  | None -> find_proofs_dir ()

let rocq_check vfile =
  let r dir =
    [ "-R"; Filename.quote (Filename.concat proofs_dir dir); "Jasmin" ]
  in
  let log = Filename.temp_file "rocq" ".log" in
  let args =
    ("rocq" :: "c" :: r "lang")
    @ r "compiler" @ r "arch" @ r "3rdparty" @ r "ssrmisc"
    @ [ "-q"; Filename.quote vfile ]
  in
  let cmd = String.concat " " args ^ " > " ^ Filename.quote log ^ " 2>&1" in
  let rc = Sys.command cmd in
  if rc <> 0 then begin
    let ic = open_in log in
    (try
       while true do
         prerr_endline (input_line ic)
       done
     with End_of_file -> ());
    close_in ic
  end;
  (try Sys.remove log with _ -> ());
  rc

let cleanup_artifacts vfile =
  let base = Filename.remove_extension vfile in
  List.iter
    (fun ext -> try Sys.remove (base ^ ext) with _ -> ())
    [ (* TODO ".v"; *) ".vo"; ".vos"; ".vok"; ".glob"; ".aux" ]

let load_and_print n name =
  Format.printf "File %s: " name;
  let p = load_file (Filename.concat path name) in
  let out_name = Filename.remove_extension name ^ ".v" in
  let oc = open_out out_name in
  let fmt = Format.formatter_of_out_channel oc in
  match
    ToRocq.extract ~imports:true Utils.X86_64 Arch.reg_size Arch.msf_size
      Arch.asmOp Arch.pp_extended_op_for_rocq p "p" fmt
  with
  | () ->
      Format.pp_print_flush fmt ();
      close_out oc;
      let rc = rocq_check out_name in
      cleanup_artifacts out_name;
      if rc = 0 then begin
        Format.printf "OK@.";
        n
      end
      else begin
        Format.printf "rocq failed@.";
        n + 1
      end
  | exception e ->
      close_out_noerr oc;
      cleanup_artifacts out_name;
      Format.eprintf "Extraction failed: %s@." (Printexc.to_string e);
      n + 1

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.fold_left load_and_print 0 cases |> exit
