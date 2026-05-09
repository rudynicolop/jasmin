open Jasmin
open Common

let rec find_named_dirs base target =
  if not (Sys.file_exists base && Sys.is_directory base) then []
  else
    Sys.readdir base |> Array.to_list
    |> List.concat_map (fun entry ->
           let path = Filename.concat base entry in
           if Sys.is_directory path then
             if entry = target then [ path ]
             else find_named_dirs path target
           else [])

let make_out_name dir name =
  let path_parts p =
    String.split_on_char '/' p
    |> List.filter (fun s -> s <> ".." && s <> "." && s <> "")
  in
  let key =
    String.concat "_" (path_parts dir @ [ Filename.remove_extension name ])
  in
  (ToRocq.rocq_sanitize_s key) ^ ".v"

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

let generate (dir, name) =
  let full_path = Filename.concat dir name in
  let p = load_file full_path in
  let out_name = make_out_name dir name in
  let oc = open_out out_name in
  let fmt = Format.formatter_of_out_channel oc in
  match
    ToRocq.extract ~imports:true Utils.X86_64 Arch.reg_size Arch.msf_size
      Arch.asmOp Arch.pp_extended_op_for_rocq p "p" fmt
  with
  | () ->
      Format.pp_print_flush fmt ();
      close_out oc;
      Some (full_path, out_name)
  | exception e ->
      close_out_noerr oc;
      cleanup_artifacts out_name;
      Mutex.lock print_mutex;
      Format.eprintf "File %s: extraction failed: %s@." full_path
        (Printexc.to_string e);
      Mutex.unlock print_mutex;
      None

let check full_path out_name =
  let rc, errors = rocq_check out_name in
  cleanup_artifacts out_name;
  Mutex.lock print_mutex;
  Format.printf "File %s: %s@." full_path (if rc = 0 then "OK" else "rocq failed");
  List.iter prerr_endline errors;
  Mutex.unlock print_mutex;
  rc

let () =
  let dirs =
    find_named_dirs "../../examples" "x86-64"
    @ find_named_dirs "../success" "x86-64"
    @ find_named_dirs "../success" "common"
    |> List.sort_uniq String.compare
  in
  let cases =
    dirs
    |> List.concat_map (fun dir ->
           Sys.readdir dir |> Array.to_list
           |> List.filter_map (fun name ->
                  let full = Filename.concat dir name in
                  if (not (Sys.is_directory full)) && Filename.check_suffix name ".jazz"
                  then Some (dir, name)
                  else None))
    |> List.sort compare
  in
  let jobs =
    List.filter_map
      (fun file ->
        match generate file with
        | Some r -> Some r
        | None -> None)
      cases
  in
  let threads =
    List.map
      (fun (full_path, out_name) ->
        let result = ref 1 in
        let t =
          Thread.create
            (fun () ->
              acquire ();
              let rc = check full_path out_name in
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
