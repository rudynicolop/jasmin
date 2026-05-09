open Jasmin
open Common

let path = "../success/x86-64"

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
  let errors =
    if rc <> 0 then begin
      let ic = open_in log in
      let lines = ref [] in
      (try
         while true do
           lines := input_line ic :: !lines
         done
       with End_of_file -> ());
      close_in ic;
      List.rev !lines
    end
    else []
  in
  (try Sys.remove log with _ -> ());
  (rc, errors)

let cleanup_artifacts vfile =
  let base = Filename.remove_extension vfile in
  List.iter
    (fun ext -> try Sys.remove (base ^ ext) with _ -> ())
    [ ".v"; ".vo"; ".vos"; ".vok"; ".glob"; ".aux" ]

let print_mutex = Mutex.create ()
let max_threads = 4
let active = ref 0
let active_mutex = Mutex.create ()
let active_cond = Condition.create ()

let acquire () =
  Mutex.lock active_mutex;
  while !active >= max_threads do
    Condition.wait active_cond active_mutex
  done;
  incr active;
  Mutex.unlock active_mutex

let release () =
  Mutex.lock active_mutex;
  decr active;
  Condition.signal active_cond;
  Mutex.unlock active_mutex

let generate name =
  let p = load_file (Filename.concat path name) in
  let out_name =
    (Filename.remove_extension name |> ToRocq.rocq_sanitize_s) ^ ".v"
  in
  let oc = open_out out_name in
  let fmt = Format.formatter_of_out_channel oc in
  match
    ToRocq.extract ~imports:true Utils.X86_64 Arch.reg_size Arch.msf_size
      Arch.asmOp Arch.pp_extended_op_for_rocq p "p" fmt
  with
  | () ->
      Format.pp_print_flush fmt ();
      close_out oc;
      Some out_name
  | exception e ->
      close_out_noerr oc;
      cleanup_artifacts out_name;
      Mutex.lock print_mutex;
      Format.eprintf "File %s: extraction failed: %s@." name
        (Printexc.to_string e);
      Mutex.unlock print_mutex;
      None

let check name out_name =
  let rc, errors = rocq_check out_name in
  cleanup_artifacts out_name;
  Mutex.lock print_mutex;
  Format.printf "File %s: %s@." name (if rc = 0 then "OK" else "rocq failed");
  List.iter prerr_endline errors;
  Mutex.unlock print_mutex;
  rc

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  let jobs =
    Array.to_list cases
    |> List.filter_map (fun name ->
        match generate name with
        | Some out_name -> Some (name, out_name)
        | None -> None)
  in
  let threads =
    List.map
      (fun (name, out_name) ->
        let result = ref 1 in
        let t =
          Thread.create
            (fun () ->
              acquire ();
              let rc = check name out_name in
              release ();
              result := rc;
              if rc <> 0 then exit rc)
            ()
        in
        (t, result))
      jobs
  in
  let errors =
    List.fold_left
      (fun n (t, result) ->
        Thread.join t;
        n + !result)
      0 threads
  in
  exit errors
