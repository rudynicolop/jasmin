open Jasmin

let rec find_named_dirs base target =
  if not (Sys.file_exists base && Sys.is_directory base) then []
  else
    Sys.readdir base |> Array.to_list
    |> List.concat_map (fun entry ->
        let path = Filename.concat base entry in
        if Sys.is_directory path then
          if entry = target then [ path ] else find_named_dirs path target
        else [])

let path_parts p =
  String.split_on_char '/' p
  |> List.filter (fun s -> s <> ".." && s <> "." && s <> "")

let make_out_name arch_dir dir name =
  let key =
    String.concat "_"
      ((arch_dir :: path_parts dir) @ [ Filename.remove_extension name ])
  in
  ToRocq.rocq_sanitize_s key ^ ".v"

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
  let r dir m = [ "-R"; Filename.quote (Filename.concat proofs_dir dir); m ] in
  let log = Filename.temp_file "rocq" ".log" in
  let args =
    [ "rocq"; "c" ] @ r "lang" "Jasmin" @ r "compiler" "Jasmin"
    @ r "arch" "Jasmin" @ r "3rdparty" "Jasmin" @ r "ssrmisc" "Jasmin"
    @ r "printing" "Printing"
    @ [ "-q"; "-w"; "-all"; Filename.quote vfile ]
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

(* Shared semaphore across all architectures so total parallelism stays at max_threads *)
let max_threads = 8
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

let find_dirs arch_dir =
  find_named_dirs "../../examples" arch_dir
  @ find_named_dirs "../success" arch_dir
  @ find_named_dirs "../success" "common"
  |> List.sort_uniq String.compare

(* -------------------------------------------------------------------- *)
(* Per-architecture driver *)

module type ArchDriver = sig
  val arch : Utils.architecture
  val dir_name : string

  module A : Arch_full.Arch

  val load_file : string -> (unit, A.extended_op) Prog.prog
end

module RunArch (D : ArchDriver) = struct
  let generate (dir, name) =
    let full_path = Filename.concat dir name in
    let p = D.load_file full_path in
    let out_name = make_out_name D.dir_name dir name in
    let oc = open_out out_name in
    let fmt = Format.formatter_of_out_channel oc in
    match ToRocq.extract D.arch D.A.pp_extended_op_for_rocq p "p" fmt with
    | () ->
        Format.pp_print_flush fmt ();
        close_out oc;
        Some (full_path, out_name)
    | exception e ->
        close_out_noerr oc;
        cleanup_artifacts out_name;
        Format.eprintf "File %s: extraction failed: %s@." full_path
          (Printexc.to_string e);
        None

  let check out_name =
    let rc, errors = rocq_check out_name in
    cleanup_artifacts out_name;
    (rc, errors)

  let run () =
    let dirs = find_dirs D.dir_name in
    let cases =
      dirs
      |> List.concat_map (fun dir ->
          Sys.readdir dir |> Array.to_list
          |> List.filter_map (fun name ->
              let full = Filename.concat dir name in
              if
                (not (Sys.is_directory full))
                && Filename.check_suffix name ".jazz"
              then Some (dir, name)
              else None))
      |> List.sort compare
    in
    let jobs = List.filter_map generate cases in
    let threads =
      List.map
        (fun (full_path, out_name) ->
          let result = ref (1, []) in
          let t =
            Thread.create
              (fun () ->
                acquire ();
                result := check out_name;
                release ())
              ()
          in
          (t, full_path, result))
        jobs
    in
    let results =
      List.map
        (fun (t, full_path, result) ->
          Thread.join t;
          (full_path, !result))
        threads
      |> List.sort (fun (a, _) (b, _) -> String.compare a b)
    in
    List.fold_left
      (fun n (full_path, (rc, errors)) ->
        if rc = 0 then Format.printf "File %s: OK@." full_path
        else begin
          Format.eprintf "File %s: rocq failed@." full_path;
          List.iter prerr_endline errors
        end;
        n + rc)
      0 results
end

(* -------------------------------------------------------------------- *)
(* Architecture instances *)

module CX86 =
  Common.Make
    ((val CoreArchFactory.core_arch_x86 ~use_lea:true ~use_set0:true
            Glob_options.Linux))

module DX86 : ArchDriver = struct
  let arch = Utils.X86_64
  let dir_name = "x86-64"

  module A = CX86.Arch

  let load_file = CX86.load_file
end

module CARM = Common.Make (CoreArchFactory.Core_arch_ARM)

module DARM : ArchDriver = struct
  let arch = Utils.ARM_M4
  let dir_name = "arm-m4"

  module A = CARM.Arch

  let load_file = CARM.load_file
end

module CRV = Common.Make (CoreArchFactory.Core_arch_RISCV)

module DRV : ArchDriver = struct
  let arch = Utils.RISCV
  let dir_name = "risc-v"

  module A = CRV.Arch

  let load_file = CRV.load_file
end

module RX86 = RunArch (DX86)
module RARM = RunArch (DARM)
module RRV = RunArch (DRV)

let () =
  let errors = RX86.run () + RARM.run () + RRV.run () in
  exit errors
