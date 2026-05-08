open Utils
open Prog
open Wsize
open Operators

module F = Format
module SS = Set.Make(String)

let sanitize_c c =
  if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_'

let sanitize_s = String.map sanitize_c

let sanitize_v v = sanitize_s (v.v_name ^ string_of_uid v.v_id)
let sanitize_fn fn = sanitize_s (fn.fn_name ^ string_of_uid fn.fn_id)

(* Name for variables. *)
let pp_var fmt v = F.fprintf fmt "%s" (sanitize_v v)

(* Name for functions. *)
let pp_fn fmt fn = F.fprintf fmt "%s" (sanitize_fn fn)

(* Name for function declarations. *)
let pp_fd_name fmt fn = F.fprintf fmt "fd_%a" pp_fn fn


(* -------------------------------------------------------------------- *)
(* Helpers *)

let pp_list pp fmt =
  let pp_sep fmt () = F.fprintf fmt ";@ " in
  F.fprintf fmt "[:: @[<hov>%a@] ]" (F.pp_print_list ~pp_sep pp)

let pp_option pp =
  let none fmt () = F.fprintf fmt "None" in
  let some fmt a = F.fprintf fmt "(Some %a)" pp a in
  F.pp_print_option ~none some

let pp_string fmt s =
  F.fprintf fmt "%S" s

let pp_z fmt z =
  F.fprintf fmt "(%a)%%Z" Z.pp_print z

let pp_positive fmt p =
  F.fprintf fmt "%a%%positive" Z.pp_print (Conv.z_of_pos p)

(* -------------------------------------------------------------------- *)
(* Wsize *)

let pp_wsize fmt = function
  | U8   -> F.fprintf fmt "U8"
  | U16  -> F.fprintf fmt "U16"
  | U32  -> F.fprintf fmt "U32"
  | U64  -> F.fprintf fmt "U64"
  | U128 -> F.fprintf fmt "U128"
  | U256 -> F.fprintf fmt "U256"

(* -------------------------------------------------------------------- *)
(* Signedness *)

let pp_signedness fmt = function
  | Signed   -> F.fprintf fmt "Signed"
  | Unsigned -> F.fprintf fmt "Unsigned"

(* -------------------------------------------------------------------- *)
(* Types *)

let pp_atype fmt = function
  | Bty Bool  -> F.fprintf fmt "abool"
  | Bty Int   -> F.fprintf fmt "aint"
  | Bty (U ws) -> F.fprintf fmt "(aword %a)" pp_wsize ws
  | Arr (ws, n) -> F.fprintf fmt "(aarr %a %d)" pp_wsize ws n

(* -------------------------------------------------------------------- *)
(* Aligned *)

let pp_aligned fmt = function
  | Memory_model.Aligned   -> F.fprintf fmt "Aligned"
  | Memory_model.Unaligned -> F.fprintf fmt "Unaligned"

(* -------------------------------------------------------------------- *)
(* Array access *)

let pp_arr_access fmt = function
  | Warray_.AAscale  -> F.fprintf fmt "AAscale"
  | Warray_.AAdirect -> F.fprintf fmt "AAdirect"

(* -------------------------------------------------------------------- *)
(* Assgn tag *)

let pp_assgn_tag fmt = function
  | Expr.AT_none    -> F.fprintf fmt "AT_none"
  | Expr.AT_keep    -> F.fprintf fmt "AT_keep"
  | Expr.AT_rename  -> F.fprintf fmt "AT_rename"
  | Expr.AT_inline  -> F.fprintf fmt "AT_inline"
  | Expr.AT_phinode -> F.fprintf fmt "AT_phinode"

(* -------------------------------------------------------------------- *)
(* Align *)

let pp_align fmt = function
  | Expr.Align   -> F.fprintf fmt "Align"
  | Expr.NoAlign -> F.fprintf fmt "NoAlign"

(* -------------------------------------------------------------------- *)
(* Direction *)

let pp_dir fmt = function
  | Expr.UpTo   -> F.fprintf fmt "UpTo"
  | Expr.DownTo -> F.fprintf fmt "DownTo"

let pp_var_i fmt v = pp_var fmt (L.unloc v)

let pp_gvar fmt v = pp_var_i fmt v.gv

(* -------------------------------------------------------------------- *)
(* Op_kind *)

let pp_op_kind fmt = function
  | Op_int  -> F.fprintf fmt "Op_int"
  | Op_w ws -> F.fprintf fmt "(Op_w %a)" pp_wsize ws

(* -------------------------------------------------------------------- *)
(* Cmp_kind *)

let pp_cmp_kind fmt = function
  | Cmp_int -> F.fprintf fmt "Cmp_int"
  | Cmp_w (s, ws) -> F.fprintf fmt "(Cmp_w %a %a)" pp_signedness s pp_wsize ws

(* -------------------------------------------------------------------- *)
(* Velem / pelem *)

let pp_pelem fmt = function
  | PE1   -> F.fprintf fmt "PE1"
  | PE2   -> F.fprintf fmt "PE2"
  | PE4   -> F.fprintf fmt "PE4"
  | PE8   -> F.fprintf fmt "PE8"
  | PE16  -> F.fprintf fmt "PE16"
  | PE32  -> F.fprintf fmt "PE32"
  | PE64  -> F.fprintf fmt "PE64"
  | PE128 -> F.fprintf fmt "PE128"

let pp_velem fmt = function
  | VE8  -> F.fprintf fmt "VE8"
  | VE16 -> F.fprintf fmt "VE16"
  | VE32 -> F.fprintf fmt "VE32"
  | VE64 -> F.fprintf fmt "VE64"

(* -------------------------------------------------------------------- *)
(* Helpers for printing Rocq constructors with their arguments.
   Used by architecture-specific asm_op printers. *)

(* TODO fmt should go as the first argument *)

let pp_bare name fmt = F.fprintf fmt "%s" name

let pp_with_ws name fmt ws =
  F.fprintf fmt "(%s %a)" name pp_wsize ws

let pp_with_ws2 name fmt (ws1, ws2) =
  F.fprintf fmt "(%s %a %a)" name pp_wsize ws1 pp_wsize ws2

let pp_ve name fmt ve =
  F.fprintf fmt "(%s %a)" name pp_velem ve

let pp_ve_ws name fmt (ve, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_velem ve pp_wsize ws

let pp_s_ws name fmt (s, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_signedness s pp_wsize ws

let pp_reg_kind fmt = function
  | Wsize.Normal -> F.fprintf fmt "Normal"
  | Wsize.Extra  -> F.fprintf fmt "Extra"

let pp_rk_ws name fmt (rk, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_reg_kind rk pp_wsize ws

let pp_ve_ws_ve_ws name fmt (ve1, ws1, ve2, ws2) =
  F.fprintf fmt "(%s %a %a %a %a)" name
    pp_velem ve1 pp_wsize ws1 pp_velem ve2 pp_wsize ws2

(* -------------------------------------------------------------------- *)
(* Unary operators *)

let pp_wiop1 fmt = function
  | WIwint_of_int ws  -> F.fprintf fmt "(WIwint_of_int %a)" pp_wsize ws
  | WIint_of_wint ws  -> F.fprintf fmt "(WIint_of_wint %a)" pp_wsize ws
  | WIword_of_wint ws -> F.fprintf fmt "(WIword_of_wint %a)" pp_wsize ws
  | WIwint_of_word ws -> F.fprintf fmt "(WIwint_of_word %a)" pp_wsize ws
  | WIwint_ext (szo, szi) -> F.fprintf fmt "(WIwint_ext %a %a)" pp_wsize szo pp_wsize szi
  | WIneg ws          -> F.fprintf fmt "(WIneg %a)" pp_wsize ws

let pp_sop1 fmt = function
  | Oword_of_int ws    -> F.fprintf fmt "(Oword_of_int %a)" pp_wsize ws
  | Oint_of_word (s,ws) -> F.fprintf fmt "(Oint_of_word %a %a)" pp_signedness s pp_wsize ws
  | Osignext (szo, szi) -> F.fprintf fmt "(Osignext %a %a)" pp_wsize szo pp_wsize szi
  | Ozeroext (szo, szi) -> F.fprintf fmt "(Ozeroext %a %a)" pp_wsize szo pp_wsize szi
  | Onot                -> F.fprintf fmt "Onot"
  | Olnot ws           -> F.fprintf fmt "(Olnot %a)" pp_wsize ws
  | Oneg k             -> F.fprintf fmt "(Oneg %a)" pp_op_kind k
  | Owi1 (sg, o)       -> F.fprintf fmt "(Owi1 %a %a)" pp_signedness sg pp_wiop1 o

(* -------------------------------------------------------------------- *)
(* Binary operators *)

let pp_wiop2 fmt = function
  | WIadd -> F.fprintf fmt "WIadd"
  | WImul -> F.fprintf fmt "WImul"
  | WIsub -> F.fprintf fmt "WIsub"
  | WIdiv -> F.fprintf fmt "WIdiv"
  | WImod -> F.fprintf fmt "WImod"
  | WIshl -> F.fprintf fmt "WIshl"
  | WIshr -> F.fprintf fmt "WIshr"
  | WIeq  -> F.fprintf fmt "WIeq"
  | WIneq -> F.fprintf fmt "WIneq"
  | WIlt  -> F.fprintf fmt "WIlt"
  | WIle  -> F.fprintf fmt "WIle"
  | WIgt  -> F.fprintf fmt "WIgt"
  | WIge  -> F.fprintf fmt "WIge"

let pp_sop2 fmt = function
  | Obeq    -> F.fprintf fmt "Obeq"
  | Oand    -> F.fprintf fmt "Oand"
  | Oor     -> F.fprintf fmt "Oor"
  | Oadd k  -> F.fprintf fmt "(Oadd %a)" pp_op_kind k
  | Omul k  -> F.fprintf fmt "(Omul %a)" pp_op_kind k
  | Osub k  -> F.fprintf fmt "(Osub %a)" pp_op_kind k
  | Odiv (s, k) -> F.fprintf fmt "(Odiv %a %a)" pp_signedness s pp_op_kind k
  | Omod (s, k) -> F.fprintf fmt "(Omod %a %a)" pp_signedness s pp_op_kind k
  | Oland ws -> F.fprintf fmt "(Oland %a)" pp_wsize ws
  | Olor ws  -> F.fprintf fmt "(Olor %a)" pp_wsize ws
  | Olxor ws -> F.fprintf fmt "(Olxor %a)" pp_wsize ws
  | Olsr ws  -> F.fprintf fmt "(Olsr %a)" pp_wsize ws
  | Olsl k   -> F.fprintf fmt "(Olsl %a)" pp_op_kind k
  | Oasr k   -> F.fprintf fmt "(Oasr %a)" pp_op_kind k
  | Oror ws  -> F.fprintf fmt "(Oror %a)" pp_wsize ws
  | Orol ws  -> F.fprintf fmt "(Orol %a)" pp_wsize ws
  | Oeq k    -> F.fprintf fmt "(Oeq %a)" pp_op_kind k
  | Oneq k   -> F.fprintf fmt "(Oneq %a)" pp_op_kind k
  | Olt k    -> F.fprintf fmt "(Olt %a)" pp_cmp_kind k
  | Ole k    -> F.fprintf fmt "(Ole %a)" pp_cmp_kind k
  | Ogt k    -> F.fprintf fmt "(Ogt %a)" pp_cmp_kind k
  | Oge k    -> F.fprintf fmt "(Oge %a)" pp_cmp_kind k
  | Ovadd (ve, ws) -> F.fprintf fmt "(Ovadd %a %a)" pp_velem ve pp_wsize ws
  | Ovsub (ve, ws) -> F.fprintf fmt "(Ovsub %a %a)" pp_velem ve pp_wsize ws
  | Ovmul (ve, ws) -> F.fprintf fmt "(Ovmul %a %a)" pp_velem ve pp_wsize ws
  | Ovlsr (ve, ws) -> F.fprintf fmt "(Ovlsr %a %a)" pp_velem ve pp_wsize ws
  | Ovlsl (ve, ws) -> F.fprintf fmt "(Ovlsl %a %a)" pp_velem ve pp_wsize ws
  | Ovasr (ve, ws) -> F.fprintf fmt "(Ovasr %a %a)" pp_velem ve pp_wsize ws
  | Owi2 (sg, ws, o) -> F.fprintf fmt "(Owi2 %a %a %a)" pp_signedness sg pp_wsize ws pp_wiop2 o

(* -------------------------------------------------------------------- *)
(* N-ary operators *)

let pp_combine_flags fmt = function
  | CF_LT s -> F.fprintf fmt "(CF_LT %a)" pp_signedness s
  | CF_LE s -> F.fprintf fmt "(CF_LE %a)" pp_signedness s
  | CF_EQ   -> F.fprintf fmt "CF_EQ"
  | CF_NEQ  -> F.fprintf fmt "CF_NEQ"
  | CF_GE s -> F.fprintf fmt "(CF_GE %a)" pp_signedness s
  | CF_GT s -> F.fprintf fmt "(CF_GT %a)" pp_signedness s

let pp_opN fmt = function
  | Opack (ws, pe) -> F.fprintf fmt "(Opack %a %a)" pp_wsize ws pp_pelem pe
  | Oarray len     -> F.fprintf fmt "(Oarray %a)" pp_positive len
  | Ocombine_flags c -> F.fprintf fmt "(Ocombine_flags %a)" pp_combine_flags c

let pp_opN_safety fmt = function
  | Ois_arr_init len  -> F.fprintf fmt "(Ois_arr_init %a)" pp_positive len
  | Ois_barr_init len -> F.fprintf fmt "(Ois_barr_init %a)" pp_positive len

(* -------------------------------------------------------------------- *)
(* Sopn *)

let pp_spill_op fmt = function
  | Pseudo_operator.Spill   -> F.fprintf fmt "Spill"
  | Pseudo_operator.Unspill -> F.fprintf fmt "Unspill"

let pp_cil_atype fmt = function
  | Type.Coq_abool -> F.fprintf fmt "abool"
  | Type.Coq_aint  -> F.fprintf fmt "aint"
  | Type.Coq_aword ws -> F.fprintf fmt "(aword %a)" pp_wsize ws
  | Type.Coq_aarr (ws, p) -> F.fprintf fmt "(aarr %a %a)" pp_wsize ws pp_positive p

let pp_pseudo_operator fmt = function
  | Pseudo_operator.Ospill (o, tys) ->
    F.fprintf fmt "(Ospill %a %a)" pp_spill_op o (pp_list pp_cil_atype) tys
  | Pseudo_operator.Ocopy (ws, p) ->
    F.fprintf fmt "(Ocopy %a %a)" pp_wsize ws pp_positive p
  | Pseudo_operator.Odeclassify ty ->
    F.fprintf fmt "(Odeclassify %a)" pp_cil_atype ty
  | Pseudo_operator.Odeclassify_mem p ->
    F.fprintf fmt "(Odeclassify_mem %a)" pp_positive p
  | Pseudo_operator.Onop -> F.fprintf fmt "Onop"
  | Pseudo_operator.Omulu ws ->
    F.fprintf fmt "(Omulu %a)" pp_wsize ws
  | Pseudo_operator.Oaddcarry ws ->
    F.fprintf fmt "(Oaddcarry %a)" pp_wsize ws
  | Pseudo_operator.Osubcarry ws ->
    F.fprintf fmt "(Osubcarry %a)" pp_wsize ws
  | Pseudo_operator.Oswap ty ->
    F.fprintf fmt "(Oswap %a)" pp_cil_atype ty

let pp_slh_op fmt = function
  | Slh_ops.SLHinit -> F.fprintf fmt "SLHinit"
  | Slh_ops.SLHupdate -> F.fprintf fmt "SLHupdate"
  | Slh_ops.SLHmove -> F.fprintf fmt "SLHmove"
  | Slh_ops.SLHprotect ws ->
    F.fprintf fmt "(SLHprotect %a)" pp_wsize ws
  | Slh_ops.SLHprotect_ptr (ws, p) ->
    F.fprintf fmt "(SLHprotect_ptr %a %a)" pp_wsize ws pp_positive p
  | Slh_ops.SLHprotect_ptr_fail (ws, p) ->
    F.fprintf fmt "(SLHprotect_ptr_fail %a %a)" pp_wsize ws pp_positive p

let pp_sopn pp_asm_op fmt = function
  | Sopn.Opseudo_op o ->
    F.fprintf fmt "(Opseudo_op %a)" pp_pseudo_operator o
  | Sopn.Oslh o ->
    F.fprintf fmt "(Oslh %a)" pp_slh_op o
  | Sopn.Oasm o ->
    F.fprintf fmt "(Oasm %a)" pp_asm_op o

(* -------------------------------------------------------------------- *)
(* Syscall *)

let pp_syscall fmt (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes (ws, n) ->
    F.fprintf fmt "(RandomBytes (%a, %a))" pp_wsize ws pp_positive n

(* -------------------------------------------------------------------- *)
(* Expressions *)

let rec pp_expr fmt = function
  | Pconst z ->
    F.fprintf fmt "(Pconst %a)" pp_z z

  | Pbool b ->
    F.fprintf fmt "(Pbool %b)" b

  | Parr_init (ws, n) ->
    F.fprintf fmt "(Parr_init %a %d)" pp_wsize ws n

  | Pvar gv ->
    F.fprintf fmt "(Pvar %a)" pp_gvar gv

  | Pget (al, aa, ws, gv, e) ->
    F.fprintf fmt "@[<hov 2>(Pget %a %a %a@ %a@ %a)@]"
      pp_aligned al pp_arr_access aa pp_wsize ws pp_gvar gv pp_expr e

  | Psub (aa, ws, len, gv, e) ->
    F.fprintf fmt "@[<hov 2>(Psub %a %a %d@ %a@ %a)@]"
      pp_arr_access aa pp_wsize ws len pp_gvar gv pp_expr e

  | Pload (al, ws, e) ->
    F.fprintf fmt "@[<hov 2>(Pload %a %a@ %a)@]"
      pp_aligned al pp_wsize ws pp_expr e

  | Papp1 (op, e) ->
    F.fprintf fmt "@[<hov 2>(Papp1 %a@ %a)@]"
      pp_sop1 op pp_expr e

  | Papp2 (op, e1, e2) ->
    F.fprintf fmt "@[<hov 2>(Papp2 %a@ %a@ %a)@]"
      pp_sop2 op pp_expr e1 pp_expr e2

  | PappN (op, es) ->
    F.fprintf fmt "@[<hov 2>(PappN %a@ %a)@]"
      pp_opN op (pp_list pp_expr) es

  | Pif (ty, e1, e2, e3) ->
    F.fprintf fmt "@[<hov 2>(Pif %a@ %a@ %a@ %a)@]"
      pp_atype ty pp_expr e1 pp_expr e2 pp_expr e3

let pp_exprs fmt es = pp_list pp_expr fmt es

(* -------------------------------------------------------------------- *)
(* Assertions *)

let rec pp_eassert fmt = function
  | Pexpr e ->
    F.fprintf fmt "(Pexpr %a)" pp_expr e

  | PappN_safety (op, es) ->
    F.fprintf fmt "@[<hov 2>(PappN_safety %a@ %a)@]"
      pp_opN_safety op (pp_list pp_expr) es

  | Pis_var_init x ->
    F.fprintf fmt "(Pis_var_init %a)" pp_var_i x

  | Pis_mem_init (e1, e2) ->
    F.fprintf fmt "@[<hov 2>(Pis_mem_init %a@ %a)@]"
      pp_expr e1 pp_expr e2

  | Pand (a1, a2) ->
    F.fprintf fmt "@[<hov 2>(Pand %a@ %a)@]"
      pp_eassert a1 pp_eassert a2

let pp_assertion fmt (label, a) =
  F.fprintf fmt "(%S, %a)" label pp_eassert a

(* -------------------------------------------------------------------- *)
(* Lvals *)

let pp_lval fmt = function
  | Lnone (_, ty) ->
    F.fprintf fmt "(Lnone dummy_var_info %a)" pp_atype ty

  | Lvar x ->
    F.fprintf fmt "(Lvar %a)" pp_var_i x

  | Lmem (al, ws, _, e) ->
    F.fprintf fmt "@[<hov 2>(Lmem %a %a dummy_var_info@ %a)@]"
      pp_aligned al pp_wsize ws pp_expr e

  | Laset (al, aa, ws, x, e) ->
    F.fprintf fmt "@[<hov 2>(Laset %a %a %a@ %a@ %a)@]"
      pp_aligned al pp_arr_access aa pp_wsize ws pp_var_i x pp_expr e

  | Lasub (aa, ws, len, x, e) ->
    F.fprintf fmt "@[<hov 2>(Lasub %a %a %d@ %a@ %a)@]"
      pp_arr_access aa pp_wsize ws len pp_var_i x pp_expr e

let pp_lvals fmt lvs = pp_list pp_lval fmt lvs

(* -------------------------------------------------------------------- *)
(* Instructions *)

let rec pp_instr_r pp_asm_op fmt = function
  | Cassgn (lv, tag, ty, e) ->
    F.fprintf fmt "@[<hov 2>(Cassgn %a@ %a %a@ %a)@]"
      pp_lval lv pp_assgn_tag tag pp_atype ty pp_expr e

  | Copn (lvs, tag, op, es) ->
    F.fprintf fmt "@[<hov 2>(Copn %a@ %a %a@ %a)@]"
      pp_lvals lvs pp_assgn_tag tag (pp_sopn pp_asm_op) op pp_exprs es

  | Csyscall (lvs, sc, es) ->
    F.fprintf fmt "@[<hov 2>(Csyscall %a@ %a@ %a)@]"
      pp_lvals lvs pp_syscall sc pp_exprs es

  | Cassert (label, a) ->
    F.fprintf fmt "@[<hov 2>(Cassert %a)@]"
      pp_assertion (label, a)

  | Cif (e, c1, c2) ->
    F.fprintf fmt "@[<v 2>(Cif %a@ %a@ %a)@]"
      pp_expr e (pp_stmt pp_asm_op) c1 (pp_stmt pp_asm_op) c2

  | Cfor (x, (dir, lo, hi), c) ->
    F.fprintf fmt "@[<v 2>(Cfor %a (%a, %a, %a)@ %a)@]"
      pp_var_i x pp_dir dir pp_expr lo pp_expr hi
      (pp_stmt pp_asm_op) c

  | Cwhile (al, c1, e, _, c2) ->
    F.fprintf fmt "@[<v 2>(Cwhile %a@ %a@ %a@ dummy_instr_info@ %a)@]"
      pp_align al
      (pp_stmt pp_asm_op) c1
      pp_expr e
      (pp_stmt pp_asm_op) c2

  | Ccall (lvs, fn, es) ->
    F.fprintf fmt "@[<hov 2>(Ccall %a@ %a@ %a)@]"
      pp_lvals lvs pp_fn fn pp_exprs es

and pp_instr pp_asm_op fmt i =
  F.fprintf fmt "@[<hov 2>(MkI dummy_instr_info@ %a)@]"
    (pp_instr_r pp_asm_op) i.i_desc

and pp_stmt pp_asm_op fmt c =
  pp_list (pp_instr pp_asm_op) fmt c

(* -------------------------------------------------------------------- *)
(* Functions *)

let pp_define_vars fmt =
  let pp_k fmt k = F.fprintf fmt "%s" (if k = Global then "mk_gvar" else "mk_lvar") in
  Sv.iter (fun v ->
    F.fprintf fmt "Definition %a := %a (mk_var_i (Var %a (mkident %s))).@ "
      pp_var v
      pp_k v.v_kind
      pp_atype v.v_ty
      (string_of_uid v.v_id)
    )

let pp_fd pp_asm_op fmt fd =
  F.fprintf fmt "@[<v 2>{|@ ";
  F.fprintf fmt "f_info := FunInfo.witness;@ ";
  F.fprintf fmt "f_contract := None;@ ";
  F.fprintf fmt "f_tyin := %a;@ " (pp_list pp_atype) fd.f_tyin;
  F.fprintf fmt "f_params := %a;@ "
    (pp_list (fun fmt (x : var) ->
      F.fprintf fmt "(%a : var_i)" pp_var x)) fd.f_args;
  F.fprintf fmt "f_body :=@ @[<v 0>%a@];@ " (pp_stmt pp_asm_op) fd.f_body;
  F.fprintf fmt "f_tyout := %a;@ " (pp_list pp_atype) fd.f_tyout;
  F.fprintf fmt "f_res := %a;@ "
    (pp_list (fun fmt (x : var_i) ->
      F.fprintf fmt "(%a : var_i)" pp_var_i x)) fd.f_ret;
  F.fprintf fmt "f_extra := tt;@ ";
  F.fprintf fmt "@]|}"

let pp_define_fname fmt fn =
  F.fprintf fmt "Definition %a := mkfunname %s.@ "
    pp_fn fn
    (string_of_uid fn.fn_id)

let pp_fds pp_asm_op fmt =
  List.iter (fun fd ->
    pp_define_fname fmt fd.f_name;
    pp_define_vars fmt (vars_fc fd);
    F.fprintf fmt "Definition fd_%a :=@ %a.@ @ "
      pp_fn fd.f_name
      (pp_fd pp_asm_op) fd
  )

(* -------------------------------------------------------------------- *)
(* Globals *)

let pp_glob fmt (x, gd) =
  match gd with
  | Global.Gword (ws, w) ->
    F.fprintf fmt "(%a : var, @Gword %a (wrepr %a %a))"
      pp_var x pp_wsize ws pp_wsize ws pp_z (Conv.z_of_word ws w)
  | Global.Garr (p, t) ->
    let ws, arr = Conv.to_array x.v_ty p t in
    let ws_bytes = int_of_ws ws / 8 in
    let n = Array.length arr in
    let total_bytes = n * ws_bytes in
    (* Extract individual bytes from each word in little-endian order *)
    let bytes = Array.make total_bytes Z.zero in
    Array.iteri (fun i w ->
      for b = 0 to ws_bytes - 1 do
        let byte_val = Z.logand (Z.shift_right w (b * 8)) (Z.of_int 255) in
        bytes.(i * ws_bytes + b) <- byte_val
      done
    ) arr;
    (* Print as nested Mz.set calls *)
    F.fprintf fmt "@[<hov 2>(%a : var,@ (@Garr %a@ {| WArray.arr_data :=@ "
      pp_var x pp_positive p;
    Array.iter (fun _byte_val ->
      F.fprintf fmt "(Mz.set@ "
    ) bytes;
    F.fprintf fmt "(Mz.empty u8)";
    Array.iteri (fun i byte_val ->
      F.fprintf fmt "@ %a@ (wrepr U8 %a))"
        pp_z (Z.of_int i) pp_z byte_val
    ) bytes;
    F.fprintf fmt "@ |}))@]"

let globs_name name = Format.sprintf "%s_gds" (sanitize_s name)

let pp_globs fmt name globs =
  F.fprintf fmt "Definition %s : glob_decls := @[<v 0>%a@].@ "
    (globs_name name)
    (pp_list pp_glob) globs

(* -------------------------------------------------------------------------- *)
(* Programs *)

let pp_prog fmt name funcs =
  let pp_fd_pair fmt fd =
    F.fprintf fmt "(%a, %a)" pp_fn fd.f_name pp_fd_name fd.f_name
  in
  F.fprintf fmt "Definition %s : uprog :=@ @[<v 0>" (sanitize_s name);
  F.fprintf fmt "  {|@ ";
  F.fprintf fmt "    p_globs := %s;@ " (globs_name name);
  F.fprintf fmt "    p_funcs := %a;@ " (pp_list pp_fd_pair) funcs;
  F.fprintf fmt "    p_extra := tt;@ "; (* TODO where to get extra from? *)
  F.fprintf fmt "  |}.@]@ "

(* -------------------------------------------------------------------------- *)
(* Imports *)

let pp_imports fmt =
  F.fprintf fmt "From Coq Require Import ZArith.@ ";
  F.fprintf fmt "From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.@ ";
  F.fprintf fmt "@ ";
  F.fprintf fmt "Require Import expr ident var type global pseudo_operator sopn arch_extra.@ "

let pp_oracles fmt =
  F.fprintf fmt "Require Import jasmin_printing.@ ";
  F.fprintf fmt "Axiom IdO : IdentOracles.@ ";
  F.fprintf fmt "Existing Instance IdO.@ "

(* Needs ident oracles *)
let pp_arch_imports fmt = function
  | X86_64 ->
    F.fprintf fmt "Require Import x86_decl x86_instr_decl x86_extra.@ ";
    F.fprintf fmt "Existing Instance x86_atoI.@ "
  | ARM_M4 -> assert false (* TODO *)
  | RISCV -> assert false (* TODO *)

(* -------------------------------------------------------------------------- *)
(* Entry point *)

let extract ?(imports=true) ?(split=false)
    arch _pd _msfsz _asmOp pp_asm_op (gd, funcs) name fmt =
  ignore imports; ignore split;
  F.fprintf fmt "@[<v 0>";
  pp_imports fmt;
  F.fprintf fmt "@ ";
  pp_oracles fmt;
  F.fprintf fmt "@ ";
  pp_arch_imports fmt arch;
  F.fprintf fmt "@ ";
  (* ------------------------------------------------ *)
  (* TODO isn't this coercion defined somewhere? *)
  F.fprintf fmt "Coercion gv : gvar >-> var_i.";
  F.fprintf fmt "@ ";
  (* ------------------------------------------------ *)
  pp_fds pp_asm_op fmt (List.rev funcs);
  F.fprintf fmt "@ ";
  pp_globs fmt name gd;
  F.fprintf fmt "@ ";
  pp_prog fmt name funcs;
  F.fprintf fmt "@]"
