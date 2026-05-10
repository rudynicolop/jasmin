open Utils
open Prog
open Wsize
open Operators
module F = Format

let error_empty_name () =
  hierror ~loc:Lnone ~kind:"compilation error" ~sub_kind:"to Rocq"
    ~internal:true
    "internal error: empty identifier while sanitizing Rocq names"

let randombytes_invalid_args loc =
  hierror ~loc:(Lone loc.L.base_loc) ~kind:"compilation error"
    ~sub_kind:"to Rocq" ~internal:true
    "internal error: RandomBytes syscall has invalid arguments"

(* -------------------------------------------------------------------------- *)
(* Identifiers *)

(* The lexer only allows these for identifiers, but the compiler may introduce
   names with other characters (e.g., periods). *)
let is_ident_c c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9')
  || c = '_'

(* Rocq identifiers must start with one of these. *)
let is_ident_start_c c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

let rocq_sanitize_c c = if is_ident_c c then c else '_'

let rocq_keywords =
  [
    "_";
    "Axiom";
    "CoFixpoint";
    "Definition";
    "Fixpoint";
    "Hypothesis";
    "Parameter";
    "Prop";
    "SProp";
    "Set";
    "Theorem";
    "Type";
    "Variable";
    "as";
    "at";
    "cofix";
    "else";
    "end";
    "fix";
    "for";
    "forall";
    "fun";
    "if";
    "in";
    "let";
    "match";
    "return";
    "then";
    "where";
    "with";
  ]
  @ [ (* Prelude *) "by"; "exists"; "exists2"; "using" ]
  @ [ (* ssreflect *) "of"; "is" ]
  |> Ss.of_list

let is_rocq_reserved s =
  Ss.mem s rocq_keywords || (s.[0] = '_' && s.[String.length s - 1] = '_')

(* Produce a valid Rocq identifier from [s]. *)
let rocq_sanitize_s s =
  if s = "" then error_empty_name ()
  else
    let s = String.map rocq_sanitize_c s in
    let s = if is_ident_start_c s.[0] then s else "_" ^ s in
    if is_rocq_reserved s then "s_" ^ s else s

let smart_sanitize id name =
  let tbl = Hid.create 101 in
  let seen = Hs.create 101 in
  fun x ->
    let i = id x in
    match Hid.find tbl i with
    | name -> name
    | exception Not_found ->
        let base = rocq_sanitize_s (name x) in
        let chosen =
          if Hs.mem seen base then base ^ "_" ^ string_of_uid i else base
        in
        Hid.add tbl (id x) (rocq_sanitize_s chosen);
        Hs.add seen chosen ();
        chosen

let rocq_sanitize_v = smart_sanitize (fun v -> v.v_id) (fun v -> v.v_name)

let rocq_sanitize_fn =
  smart_sanitize (fun fn -> fn.fn_id) (fun fn -> fn.fn_name)

(* Print the name of a [var], [var_i], [gvar] (they all print the same). *)
let pp_var fmt v = F.fprintf fmt "%s" (rocq_sanitize_v v)
let pp_var_i fmt v = pp_var fmt (L.unloc v)
let pp_gvar fmt v = pp_var_i fmt v.gv

(* We only define the Rocq [gvar] under the name [pp_var]. To access the [var_i]
   and [var], we use projections. *)
let pp_gv_var fmt v = F.fprintf fmt "%a.(gv)" pp_var v
let pp_gv_var_i fmt v = F.fprintf fmt "%a.(gv)" pp_var_i v
let pp_v_var_var fmt v = F.fprintf fmt "%a.(gv).(v_var)" pp_var v

(* Function names. *)
let pp_fn fmt fn = F.fprintf fmt "%s" (rocq_sanitize_fn fn)

(* -------------------------------------------------------------------------- *)
(* Printing helpers *)

let pp_print_nothing _fmt () = ()
let pp_newline fmt () = F.fprintf fmt "@ "

(* -------------------------------------------------------------------------- *)
(* Rocq helpers *)

let pp_comment_gen fmt pp x = F.fprintf fmt "(* %a *)@ " pp x
let pp_comment fmt = pp_comment_gen fmt F.pp_print_string

let pp_separator_gen fmt pp x =
  pp_comment fmt
    "--------------------------------------------------------------------------";
  pp_comment_gen fmt pp x;
  pp_newline fmt ()

let pp_separator fmt s = pp_separator_gen fmt F.pp_print_string s

let pp_rocq_definition_gen fmt pp_lhs lhs pp_type ty pp_rhs rhs =
  F.fprintf fmt "@[<hv 2>Definition %a : %a :=@ %a@].@ " pp_lhs lhs pp_type ty
    pp_rhs rhs

let pp_rocq_definition fmt pp_lhs lhs ty pp_rhs rhs =
  pp_rocq_definition_gen fmt pp_lhs lhs F.pp_print_string ty pp_rhs rhs

let pp_rocq_record pp fmt x = F.fprintf fmt "@[<v 0>{|@[<v 0>@ %a@]@ |}@]" pp x
let pp_rocq_bool fmt = F.fprintf fmt "%B"
let pp_rocq_z fmt z = F.fprintf fmt "(%a)%%Z" Z.pp_print z

let pp_rocq_positive fmt p =
  F.fprintf fmt "%a%%positive" Z.pp_print (Conv.z_of_pos p)

(* We are relying on the string scope being inferred, otherwise we need
   `%string`. *)
let pp_rocq_string fmt = F.fprintf fmt "%S"

let pp_rocq_seq pp fmt xs =
  if xs = [] then F.fprintf fmt "[::]"
  else
    let pp_sep fmt () =
      F.pp_print_break fmt 0 2;
      F.fprintf fmt "; "
    in
    F.fprintf fmt "@[<hv>[:: %a ]@]" (F.pp_print_list ~pp_sep pp) xs

let pp_rocq_option pp =
  let none fmt () = F.fprintf fmt "None" in
  let some fmt a = F.fprintf fmt "Some %a" pp a in
  F.pp_print_option ~none some

(* -------------------------------------------------------------------------- *)
(* Basics *)

let pp_wsize fmt = function
  | U8 -> F.fprintf fmt "U8"
  | U16 -> F.fprintf fmt "U16"
  | U32 -> F.fprintf fmt "U32"
  | U64 -> F.fprintf fmt "U64"
  | U128 -> F.fprintf fmt "U128"
  | U256 -> F.fprintf fmt "U256"

let pp_signedness fmt = function
  | Signed -> F.fprintf fmt "Signed"
  | Unsigned -> F.fprintf fmt "Unsigned"

let pp_atype fmt = function
  | Bty Bool -> F.fprintf fmt "abool"
  | Bty Int -> F.fprintf fmt "aint"
  | Bty (U ws) -> F.fprintf fmt "aword %a" pp_wsize ws
  | Arr (ws, n) -> F.fprintf fmt "aarr %a %d" pp_wsize ws n

let pp_aligned fmt = function
  | Memory_model.Aligned -> F.fprintf fmt "Aligned"
  | Unaligned -> F.fprintf fmt "Unaligned"

let pp_arr_access fmt = function
  | Warray_.AAscale -> F.fprintf fmt "AAscale"
  | AAdirect -> F.fprintf fmt "AAdirect"

let pp_align fmt = function
  | Expr.Align -> F.fprintf fmt "Align"
  | NoAlign -> F.fprintf fmt "NoAlign"

let pp_dir fmt = function
  | Expr.UpTo -> F.fprintf fmt "UpTo"
  | DownTo -> F.fprintf fmt "DownTo"

let pp_op_kind fmt = function
  | Op_int -> F.fprintf fmt "Op_int"
  | Op_w ws -> F.fprintf fmt "Op_w %a" pp_wsize ws

let pp_cmp_kind fmt = function
  | Cmp_int -> F.fprintf fmt "Cmp_int"
  | Cmp_w (s, ws) -> F.fprintf fmt "Cmp_w %a %a" pp_signedness s pp_wsize ws

let pp_pelem fmt = function
  | PE1 -> F.fprintf fmt "PE1"
  | PE2 -> F.fprintf fmt "PE2"
  | PE4 -> F.fprintf fmt "PE4"
  | PE8 -> F.fprintf fmt "PE8"
  | PE16 -> F.fprintf fmt "PE16"
  | PE32 -> F.fprintf fmt "PE32"
  | PE64 -> F.fprintf fmt "PE64"
  | PE128 -> F.fprintf fmt "PE128"

let pp_velem fmt = function
  | VE8 -> F.fprintf fmt "VE8"
  | VE16 -> F.fprintf fmt "VE16"
  | VE32 -> F.fprintf fmt "VE32"
  | VE64 -> F.fprintf fmt "VE64"

let pp_wrepr ws fmt n = F.fprintf fmt "wrepr %a %a" pp_wsize ws pp_rocq_z n
let pp_word_ty fmt ws = F.fprintf fmt "word %a" pp_wsize ws
let pp_word ws fmt w = F.fprintf fmt "%a" (pp_wrepr ws) (Conv.z_of_word ws w)

(* -------------------------------------------------------------------------- *)
(* Helpers for printing Rocq constructors with their arguments.
   Used by architecture-specific asm_op printers. *)

let pp_bare fmt name = F.fprintf fmt "%s" name
let pp_with_ws fmt name ws = F.fprintf fmt "(%s %a)" name pp_wsize ws

let pp_with_ws2 fmt name (ws1, ws2) =
  F.fprintf fmt "(%s %a %a)" name pp_wsize ws1 pp_wsize ws2

let pp_ve fmt name ve = F.fprintf fmt "(%s %a)" name pp_velem ve

let pp_ve_ws fmt name (ve, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_velem ve pp_wsize ws

let pp_s_ws fmt name (s, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_signedness s pp_wsize ws

let pp_reg_kind fmt = function
  | Wsize.Normal -> F.fprintf fmt "Normal"
  | Extra -> F.fprintf fmt "Extra"

let pp_rk_ws fmt name (rk, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_reg_kind rk pp_wsize ws

let pp_ve_ws_ve_ws fmt name (ve1, ws1, ve2, ws2) =
  F.fprintf fmt "(%s %a %a %a %a)" name pp_velem ve1 pp_wsize ws1 pp_velem ve2
    pp_wsize ws2

(* -------------------------------------------------------------------------- *)
(* Operators *)

let pp_wiop1 fmt = function
  | WIwint_of_int ws -> F.fprintf fmt "WIwint_of_int %a" pp_wsize ws
  | WIint_of_wint ws -> F.fprintf fmt "WIint_of_wint %a" pp_wsize ws
  | WIword_of_wint ws -> F.fprintf fmt "WIword_of_wint %a" pp_wsize ws
  | WIwint_of_word ws -> F.fprintf fmt "WIwint_of_word %a" pp_wsize ws
  | WIwint_ext (szo, szi) ->
      F.fprintf fmt "WIwint_ext %a %a" pp_wsize szo pp_wsize szi
  | WIneg ws -> F.fprintf fmt "WIneg %a" pp_wsize ws

let pp_sop1 fmt = function
  | Oword_of_int ws -> F.fprintf fmt "Oword_of_int %a" pp_wsize ws
  | Oint_of_word (s, ws) ->
      F.fprintf fmt "Oint_of_word %a %a" pp_signedness s pp_wsize ws
  | Osignext (szo, szi) ->
      F.fprintf fmt "Osignext %a %a" pp_wsize szo pp_wsize szi
  | Ozeroext (szo, szi) ->
      F.fprintf fmt "Ozeroext %a %a" pp_wsize szo pp_wsize szi
  | Onot -> F.fprintf fmt "Onot"
  | Olnot ws -> F.fprintf fmt "Olnot %a" pp_wsize ws
  | Oneg k -> F.fprintf fmt "Oneg (%a)" pp_op_kind k
  | Owi1 (sg, o) -> F.fprintf fmt "Owi1 %a (%a)" pp_signedness sg pp_wiop1 o

let pp_wiop2 fmt = function
  | WIadd -> F.fprintf fmt "WIadd"
  | WImul -> F.fprintf fmt "WImul"
  | WIsub -> F.fprintf fmt "WIsub"
  | WIdiv -> F.fprintf fmt "WIdiv"
  | WImod -> F.fprintf fmt "WImod"
  | WIshl -> F.fprintf fmt "WIshl"
  | WIshr -> F.fprintf fmt "WIshr"
  | WIeq -> F.fprintf fmt "WIeq"
  | WIneq -> F.fprintf fmt "WIneq"
  | WIlt -> F.fprintf fmt "WIlt"
  | WIle -> F.fprintf fmt "WIle"
  | WIgt -> F.fprintf fmt "WIgt"
  | WIge -> F.fprintf fmt "WIge"

let pp_sop2 fmt = function
  | Obeq -> F.fprintf fmt "Obeq"
  | Oand -> F.fprintf fmt "Oand"
  | Oor -> F.fprintf fmt "Oor"
  | Oadd k -> F.fprintf fmt "Oadd (%a)" pp_op_kind k
  | Omul k -> F.fprintf fmt "Omul (%a)" pp_op_kind k
  | Osub k -> F.fprintf fmt "Osub (%a)" pp_op_kind k
  | Odiv (s, k) -> F.fprintf fmt "Odiv %a (%a)" pp_signedness s pp_op_kind k
  | Omod (s, k) -> F.fprintf fmt "Omod %a (%a)" pp_signedness s pp_op_kind k
  | Oland ws -> F.fprintf fmt "Oland %a" pp_wsize ws
  | Olor ws -> F.fprintf fmt "Olor %a" pp_wsize ws
  | Olxor ws -> F.fprintf fmt "Olxor %a" pp_wsize ws
  | Olsr ws -> F.fprintf fmt "Olsr %a" pp_wsize ws
  | Olsl k -> F.fprintf fmt "Olsl (%a)" pp_op_kind k
  | Oasr k -> F.fprintf fmt "Oasr (%a)" pp_op_kind k
  | Oror ws -> F.fprintf fmt "Oror %a" pp_wsize ws
  | Orol ws -> F.fprintf fmt "Orol %a" pp_wsize ws
  | Oeq k -> F.fprintf fmt "Oeq (%a)" pp_op_kind k
  | Oneq k -> F.fprintf fmt "Oneq (%a)" pp_op_kind k
  | Olt k -> F.fprintf fmt "Olt (%a)" pp_cmp_kind k
  | Ole k -> F.fprintf fmt "Ole (%a)" pp_cmp_kind k
  | Ogt k -> F.fprintf fmt "Ogt (%a)" pp_cmp_kind k
  | Oge k -> F.fprintf fmt "Oge (%a)" pp_cmp_kind k
  | Ovadd (ve, ws) -> F.fprintf fmt "Ovadd %a %a" pp_velem ve pp_wsize ws
  | Ovsub (ve, ws) -> F.fprintf fmt "Ovsub %a %a" pp_velem ve pp_wsize ws
  | Ovmul (ve, ws) -> F.fprintf fmt "Ovmul %a %a" pp_velem ve pp_wsize ws
  | Ovlsr (ve, ws) -> F.fprintf fmt "Ovlsr %a %a" pp_velem ve pp_wsize ws
  | Ovlsl (ve, ws) -> F.fprintf fmt "Ovlsl %a %a" pp_velem ve pp_wsize ws
  | Ovasr (ve, ws) -> F.fprintf fmt "Ovasr %a %a" pp_velem ve pp_wsize ws
  | Owi2 (sg, ws, o) ->
      F.fprintf fmt "Owi2 %a %a %a" pp_signedness sg pp_wsize ws pp_wiop2 o

let pp_combine_flags fmt = function
  | CF_LT s -> F.fprintf fmt "CF_LT %a" pp_signedness s
  | CF_LE s -> F.fprintf fmt "CF_LE %a" pp_signedness s
  | CF_EQ -> F.fprintf fmt "CF_EQ"
  | CF_NEQ -> F.fprintf fmt "CF_NEQ"
  | CF_GE s -> F.fprintf fmt "CF_GE %a" pp_signedness s
  | CF_GT s -> F.fprintf fmt "CF_GT %a" pp_signedness s

let pp_opN fmt = function
  | Opack (ws, pe) -> F.fprintf fmt "Opack %a %a" pp_wsize ws pp_pelem pe
  | Oarray len -> F.fprintf fmt "Oarray %a" pp_rocq_positive len
  | Ocombine_flags c -> F.fprintf fmt "Ocombine_flags (%a)" pp_combine_flags c

let pp_opN_safety fmt = function
  | Ois_arr_init len -> F.fprintf fmt "Ois_arr_init %a" pp_rocq_positive len
  | Ois_barr_init len -> F.fprintf fmt "Ois_barr_init %a" pp_rocq_positive len

let pp_spill_op fmt = function
  | Pseudo_operator.Spill -> F.fprintf fmt "Spill"
  | Unspill -> F.fprintf fmt "Unspill"

let pp_cil_atype fmt = function
  | Type.Coq_abool -> F.fprintf fmt "abool"
  | Coq_aint -> F.fprintf fmt "aint"
  | Coq_aword ws -> F.fprintf fmt "aword %a" pp_wsize ws
  | Coq_aarr (ws, p) ->
      F.fprintf fmt "aarr %a %a" pp_wsize ws pp_rocq_positive p

let pp_pseudo_operator fmt = function
  | Pseudo_operator.Ospill (o, tys) ->
      F.fprintf fmt "Ospill %a %a" pp_spill_op o (pp_rocq_seq pp_cil_atype) tys
  | Ocopy (ws, p) -> F.fprintf fmt "Ocopy %a %a" pp_wsize ws pp_rocq_positive p
  | Odeclassify ty -> F.fprintf fmt "Odeclassify (%a)" pp_cil_atype ty
  | Odeclassify_mem p -> F.fprintf fmt "Odeclassify_mem %a" pp_rocq_positive p
  | Onop -> F.fprintf fmt "Onop"
  | Omulu ws -> F.fprintf fmt "Omulu %a" pp_wsize ws
  | Oaddcarry ws -> F.fprintf fmt "Oaddcarry %a" pp_wsize ws
  | Osubcarry ws -> F.fprintf fmt "Osubcarry %a" pp_wsize ws
  | Oswap ty -> F.fprintf fmt "Oswap (%a)" pp_cil_atype ty

let pp_slh_op fmt = function
  | Slh_ops.SLHinit -> F.fprintf fmt "SLHinit"
  | SLHupdate -> F.fprintf fmt "SLHupdate"
  | SLHmove -> F.fprintf fmt "SLHmove"
  | SLHprotect ws -> F.fprintf fmt "SLHprotect %a" pp_wsize ws
  | SLHprotect_ptr (ws, p) ->
      F.fprintf fmt "SLHprotect_ptr %a %a" pp_wsize ws pp_rocq_positive p
  | SLHprotect_ptr_fail (ws, p) ->
      F.fprintf fmt "SLHprotect_ptr_fail %a %a" pp_wsize ws pp_rocq_positive p

let pp_sopn pp_asm_op fmt = function
  | Sopn.Opseudo_op o -> F.fprintf fmt "Opseudo_op (%a)" pp_pseudo_operator o
  | Oslh o -> F.fprintf fmt "Oslh (%a)" pp_slh_op o
  | Oasm o -> F.fprintf fmt "Oasm (%a)" pp_asm_op o

(* -------------------------------------------------------------------------- *)
(* Expressions *)

let rec pp_expr fmt = function
  | Pconst z -> F.fprintf fmt "Pconst %a" pp_rocq_z z
  | Pbool b -> F.fprintf fmt "Pbool %a" pp_rocq_bool b
  | Parr_init (ws, n) -> F.fprintf fmt "Parr_init %a %d" pp_wsize ws n
  | Pvar gv -> F.fprintf fmt "Pvar %a" pp_gvar gv
  | Pget (al, aa, ws, gv, e) ->
      F.fprintf fmt "Pget %a %a %a %a (%a)" pp_aligned al pp_arr_access aa
        pp_wsize ws pp_gvar gv pp_expr e
  | Psub (aa, ws, len, gv, e) ->
      F.fprintf fmt "Psub %a %a %d %a (%a)" pp_arr_access aa pp_wsize ws len
        pp_gvar gv pp_expr e
  | Pload (al, ws, e) ->
      F.fprintf fmt "Pload %a %a (%a)" pp_aligned al pp_wsize ws pp_expr e
  | Papp1 (op, e) -> F.fprintf fmt "Papp1 (%a) (%a)" pp_sop1 op pp_expr e
  | Papp2 (op, e1, e2) ->
      F.fprintf fmt "Papp2 (%a) (%a) (%a)" pp_sop2 op pp_expr e1 pp_expr e2
  | PappN (op, es) ->
      F.fprintf fmt "PappN (%a) %a" pp_opN op (pp_rocq_seq pp_expr) es
  | Pif (ty, e1, e2, e3) ->
      F.fprintf fmt "Pif (%a) (%a) (%a) (%a)" pp_atype ty pp_expr e1 pp_expr e2
        pp_expr e3

let pp_exprs fmt es = pp_rocq_seq pp_expr fmt es

(* -------------------------------------------------------------------------- *)
(* Assertions *)

let rec pp_eassert fmt = function
  | Pexpr e -> F.fprintf fmt "Pexpr (%a)" pp_expr e
  | PappN_safety (op, es) ->
      F.fprintf fmt "PappN_safety (%a) %a" pp_opN_safety op
        (pp_rocq_seq pp_expr) es
  | Pis_var_init x -> F.fprintf fmt "Pis_var_init %a" pp_gv_var_i x
  | Pis_mem_init (e1, e2) ->
      F.fprintf fmt "Pis_mem_init (%a) (%a)" pp_expr e1 pp_expr e2
  | Pand (a1, a2) -> F.fprintf fmt "Pand (%a) (%a)" pp_eassert a1 pp_eassert a2

(* -------------------------------------------------------------------------- *)
(* Lvals *)

let pp_lval fmt = function
  | Lnone (_, ty) -> F.fprintf fmt "Lnone dummy_var_info (%a)" pp_atype ty
  | Lvar x -> F.fprintf fmt "Lvar %a" pp_gv_var_i x
  | Lmem (al, ws, _, e) ->
      F.fprintf fmt "Lmem %a %a dummy_var_info (%a)" pp_aligned al pp_wsize ws
        pp_expr e
  | Laset (al, aa, ws, x, e) ->
      F.fprintf fmt "Laset %a %a %a %a (%a)" pp_aligned al pp_arr_access aa
        pp_wsize ws pp_gv_var_i x pp_expr e
  | Lasub (aa, ws, len, x, e) ->
      F.fprintf fmt "Lasub %a %a %d %a (%a)" pp_arr_access aa pp_wsize ws len
        pp_gv_var_i x pp_expr e

let pp_lvals fmt lvs = pp_rocq_seq pp_lval fmt lvs

(* -------------------------------------------------------------------------- *)
(* Instructions *)

(* [Cif], [Cfor], and [Cwhile] always break the line, the rest never do. *)
let rec pp_instr_r ~loc pp_asm_op fmt = function
  | Cassgn (lv, _, ty, e) ->
      F.fprintf fmt "@[<h>cassgn (%a) (%a) (%a)@]" pp_lval lv pp_atype ty
        pp_expr e
  | Copn (lvs, _, op, es) ->
      F.fprintf fmt "@[<h>copn %a (%a) %a@]" pp_lvals lvs (pp_sopn pp_asm_op) op
        pp_exprs es
  | Csyscall (lvs, sc, es) -> begin
      match sc with
      | RandomBytes (ws, n) -> (
          match (lvs, es) with
          | [ lv ], [ e ] ->
              F.fprintf fmt "@[<h>crandombytes (%a) %a %a (%a)@]" pp_lval lv
                pp_wsize ws pp_rocq_positive n pp_expr e
          | _ -> randombytes_invalid_args loc)
    end
  | Cassert (label, e) ->
      F.fprintf fmt "@[<h>cassert %a (%a)@]" pp_rocq_string label pp_eassert e
  | Cif (e, c1, c2) ->
      F.fprintf fmt "@[<hv 2>cif@ (%a)@ %a@ %a@]" pp_expr e (pp_stmt pp_asm_op)
        c1 (pp_stmt pp_asm_op) c2
  | Cfor (x, (dir, lo, hi), c) ->
      F.fprintf fmt "@[<hv 2>cfor@ (%a)@ (%a, %a, %a)@ %a@]" pp_gv_var_i x
        pp_dir dir pp_expr lo pp_expr hi (pp_stmt pp_asm_op) c
  | Cwhile (al, c1, e, _, c2) ->
      F.fprintf fmt "@[<hv 2>cwhile@ (%a)@ %a@ (%a)@ %a@]" pp_align al
        (pp_stmt pp_asm_op) c1 pp_expr e (pp_stmt pp_asm_op) c2
  | Ccall (lvs, fn, es) ->
      F.fprintf fmt "@[<h>ccall %a %a %a@]" pp_lvals lvs pp_fn fn pp_exprs es

and pp_instr pp_asm_op fmt i =
  F.fprintf fmt "%a" (pp_instr_r ~loc:i.i_loc pp_asm_op) i.i_desc

and pp_stmt pp_asm_op fmt c = pp_rocq_seq (pp_instr pp_asm_op) fmt c

(* -------------------------------------------------------------------------- *)
(* Variable declarations *)

let pp_mk_ident fmt i = F.fprintf fmt "mkident %s" (string_of_uid i)

let pp_vscope fmt k =
  F.fprintf fmt "%s" (if k = Global then "Sglob" else "Slocal")

let pp_mk_gvar fmt v =
  F.fprintf fmt "mk_rocq_gvar %a (%a) (%a)" pp_vscope v.v_kind pp_atype v.v_ty
    pp_mk_ident v.v_id

let pp_gvar_definition fmt v =
  pp_rocq_definition fmt pp_var v "gvar" pp_mk_gvar v

let pp_vars_definition =
  F.pp_print_list ~pp_sep:pp_print_nothing pp_gvar_definition

(* -------------------------------------------------------------------------- *)
(* Functions *)

let pp_mk_fname fmt i = F.fprintf fmt "mkfname %s" (string_of_uid i)

let pp_fn_definition fmt fn =
  pp_rocq_definition fmt pp_fn fn "funname" pp_mk_fname fn.fn_id

let pp_fn_definitions fmt =
  F.pp_print_list ~pp_sep:pp_print_nothing pp_fn_definition fmt

let pp_f_sig pre fmt fn = F.fprintf fmt "%s_%a" pre pp_fn fn
let pp_f_tyin = pp_f_sig "tyin"
let pp_f_args = pp_f_sig "args"
let pp_f_tyout = pp_f_sig "tyout"
let pp_f_res = pp_f_sig "res"
let pp_f_body = pp_f_sig "body"

let pp_f_sig_definition pre pp_xs fmt fn xs =
  pp_rocq_definition fmt (pp_f_sig pre) fn "seq var_i" (pp_rocq_seq pp_xs) xs

let pp_f_args_definition = pp_f_sig_definition "args" pp_gv_var
let pp_f_res_definition = pp_f_sig_definition "res" pp_gv_var_i

let pp_f_sig_ty_definition pp fmt fn tys =
  pp_rocq_definition fmt pp fn "seq atype" (pp_rocq_seq pp_atype) tys

let pp_f_tyin_definition = pp_f_sig_ty_definition pp_f_tyin
let pp_f_tyout_definition = pp_f_sig_ty_definition pp_f_tyout

let pp_f_body_definition pp_asm_op fmt fn body =
  pp_rocq_definition fmt pp_f_body fn "cmd" (pp_stmt pp_asm_op) body

(* TODO fix info and contract *)
let pp_fd fmt fd =
  let pp_fields fmt fd =
    F.fprintf fmt "f_info := FunInfo.witness;@ ";
    F.fprintf fmt "f_contract := None;@ ";
    F.fprintf fmt "f_tyin := %a;@ " pp_f_tyin fd.f_name;
    F.fprintf fmt "f_params := %a;@ " pp_f_args fd.f_name;
    F.fprintf fmt "f_body := %a;@ " pp_f_body fd.f_name;
    F.fprintf fmt "f_tyout := %a;@ " pp_f_tyout fd.f_name;
    F.fprintf fmt "f_res := %a;@ " pp_f_res fd.f_name;
    F.fprintf fmt "f_extra := tt;"
  in
  pp_rocq_record pp_fields fmt fd

let pp_fd_name fmt fn = F.fprintf fmt "fd_%a" pp_fn fn

let pp_fd_defintion fmt fd =
  pp_rocq_definition fmt pp_fd_name fd.f_name "ufundef" pp_fd fd

let pp_fd_block pp_asm_op fmt fd =
  let vars = Sv.to_list (vars_fc fd) in
  pp_separator_gen fmt pp_fn fd.f_name;
  pp_comment fmt "Local variables";
  pp_vars_definition fmt vars;
  if vars <> [] then pp_newline fmt ();
  pp_comment fmt "Signature";
  pp_f_tyin_definition fmt fd.f_name fd.f_tyin;
  pp_f_args_definition fmt fd.f_name fd.f_args;
  pp_f_tyout_definition fmt fd.f_name fd.f_tyout;
  pp_f_res_definition fmt fd.f_name fd.f_ret;
  pp_newline fmt ();
  pp_comment fmt "Body";
  pp_f_body_definition pp_asm_op fmt fd.f_name fd.f_body;
  pp_newline fmt ();
  pp_fd_defintion fmt fd

let pp_fds pp_asm_op =
  F.pp_print_list ~pp_sep:pp_newline (pp_fd_block pp_asm_op)

(* -------------------------------------------------------------------- *)
(* Globals *)

let glob_bytes x p t = Conv.to_array8 x.v_ty p t |> Array.to_list
let pp_glob_data fmt v = F.fprintf fmt "%a_data" pp_var v

let pp_glob_data_definition fmt (x, gd) =
  match gd with
  | Global.Gword (ws, w) ->
      pp_rocq_definition_gen fmt pp_glob_data x pp_word_ty ws (pp_word ws) w
  | Global.Garr (p, t) ->
      let pp_bytes = pp_rocq_seq (pp_wrepr U8) in
      pp_rocq_definition fmt pp_glob_data x "seq u8" pp_bytes (glob_bytes x p t)

let pp_glob_data_block =
  F.pp_print_list ~pp_sep:pp_print_nothing pp_glob_data_definition

let pp_glob fmt (x, gd) =
  match gd with
  | Global.Gword _ ->
      F.fprintf fmt "(%a, Gword %a)" pp_v_var_var x pp_glob_data x
  | Global.Garr (p, _) ->
      F.fprintf fmt "(%a, Garr (arr_of_bytes %a %a))" pp_v_var_var x
        pp_rocq_positive p pp_glob_data x

let pp_globs fmt name = Format.fprintf fmt "%s_gds" (rocq_sanitize_s name)

let pp_globs_definition fmt name globs =
  pp_vars_definition fmt (List.map fst globs);
  if globs <> [] then pp_newline fmt ();
  pp_glob_data_block fmt globs;
  if globs <> [] then pp_newline fmt ();
  pp_rocq_definition fmt pp_globs name "glob_decls" (pp_rocq_seq pp_glob) globs

(* -------------------------------------------------------------------------- *)
(* Programs *)

(* TODO where to get extra from? *)
let pp_mk_prog name fmt funcs =
  let pp_fd_pair fmt fd =
    F.fprintf fmt "(%a, %a)" pp_fn fd.f_name pp_fd_name fd.f_name
  in
  F.fprintf fmt "p_globs := %a;@ " pp_globs name;
  F.fprintf fmt "@[<hov 2>p_funcs :=@ %a;@]@ " (pp_rocq_seq pp_fd_pair) funcs;
  F.fprintf fmt "p_extra := tt;"

let pp_prog_definition fmt name funcs =
  pp_rocq_definition fmt F.pp_print_string (rocq_sanitize_s name) "uprog"
    (pp_rocq_record (pp_mk_prog name))
    funcs

(* -------------------------------------------------------------------------- *)
(* Imports *)

let pp_imports fmt =
  F.fprintf fmt "From Coq Require Import ZArith.@ ";
  F.fprintf fmt
    "From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.@ ";
  pp_newline fmt ();
  F.fprintf fmt
    "Require Import expr ident var type global pseudo_operator sopn \
     arch_extra.@ ";
  F.fprintf fmt "From Printing Require Import atoi syntax data.@ "

let pp_oracles fmt =
  F.fprintf fmt "Axiom IdO : IdentOracles.@ ";
  F.fprintf fmt "Existing Instance IdO.@ "

let suff_of_arch = function
  | X86_64 -> "x86"
  | ARM_M4 -> "arm"
  | RISCV -> "riscv"

let pp_arch_imports fmt a =
  let s = suff_of_arch a in
  F.fprintf fmt "Require Import %s_decl %s_instr_decl %s_extra.@ " s s s;
  F.fprintf fmt "Existing Instance %s_atoI.@ " s

(* -------------------------------------------------------------------------- *)
(* Entry point *)

let pp_section_ido fmt =
  F.fprintf fmt "Section IDO.@ ";
  F.fprintf fmt "Context {IdO : IdentOracles}.@ "

let pp_end_ido fmt () = F.fprintf fmt "End IDO.@ "
let pp_require_import fmt modname = F.fprintf fmt "Require Import %s.@ " modname

let with_out_file path f =
  let oc = open_out path in
  let fmt = F.formatter_of_out_channel oc in
  F.fprintf fmt "@[<v 0>";
  (try f fmt
   with e ->
     close_out_noerr oc;
     raise e);
  F.fprintf fmt "@]";
  F.pp_print_flush fmt ();
  close_out oc

let pp_header fmt arch =
  pp_imports fmt;
  pp_newline fmt ();
  pp_arch_imports fmt arch;
  pp_newline fmt ()

let pp_oracles_block fmt =
  pp_oracles fmt;
  pp_newline fmt ()

let pp_globals_block fmt name gd =
  pp_separator fmt "Globals";
  pp_globs_definition fmt name gd;
  pp_newline fmt ()

let pp_funnames_block fmt names =
  pp_separator fmt "Function names";
  pp_fn_definitions fmt names;
  pp_newline fmt ()

let pp_fundecls_block pp_asm_op fmt funcs =
  pp_separator fmt "Functions";
  pp_fds pp_asm_op fmt funcs;
  pp_newline fmt ()

let pp_prog_block fmt name funcs =
  pp_separator fmt "Program";
  pp_prog_definition fmt name funcs

(* The globals block must come before functions because it declares the names of
   global variables used in the functions' bodies. *)
let extract arch pp_asm_op (gd, funcs) name fmt =
  let name = rocq_sanitize_s name in
  let funcs = List.rev funcs in
  F.fprintf fmt "@[<v 0>";
  pp_header fmt arch;
  pp_oracles_block fmt;
  pp_globals_block fmt name gd;
  pp_funnames_block fmt (List.map (fun fd -> fd.f_name) funcs);
  pp_fundecls_block pp_asm_op fmt funcs;
  pp_prog_block fmt name funcs;
  F.fprintf fmt "@]"

(* -------------------------------------------------------------------------- *)
(* Split files. Produces a _CoqProject and a Makefile as well. *)

let coqproject_name = "_CoqProject"
let makefile_name = "Makefile"
let globs_module_name base = rocq_sanitize_s (base ^ "_globs")
let funnames_module_name base = rocq_sanitize_s (base ^ "_funnames")

let function_module_name base fn =
  rocq_sanitize_s (base ^ "_" ^ rocq_sanitize_fn fn)

let coq_project_header =
  "-arg \"-set\" -arg \"'Uniform Inductive Parameters'\"\n\
   -arg \"-set\" -arg \"'Implicit Arguments'\"\n\
   -arg \"-unset\" -arg \"'Strict Implicit'\"\n\
   -arg \"-unset\" -arg \"'Printing Implicit Defensive'\"\n\
   -arg \"-w -notation-overridden\"\n\
   -arg \"-w -extraction-reserved-identifier\"\n\
   -arg \"-w -extraction-opaque-accessed\"\n\
   -arg \"-w -ambiguous-paths\"\n\
   -arg \"-w -redundant-canonical-projection\"\n\
   -arg \"-w -projection-no-head-constant\"\n\
   -arg \"-w -postfix-notation-not-level-1\"\n\
   -arg \"-w -deprecated-since-mathcomp-2.4.0\"\n\
   -arg \"-w -deprecated-since-mathcomp-2.5.0\"\n\
   -arg \"-w -deprecated-from-Coq\"\n\
   -arg \"-w -deprecated-dirpath-Coq\"\n\
   # can be solved only with Stdlib >= 9.1\n\
   -arg \"-w -deprecated-reference-since-9.1\"\n\
   # to be handled when requiring Rocq >= 9.3\n\
   -arg \"-w -rewrite-rw\"\n\n\
   -R ../proofs/3rdparty Jasmin\n\
   -R ../proofs/arch Jasmin\n\
   -R ../proofs/compiler Jasmin\n\
   -R ../proofs/lang Jasmin\n\
   -R ../proofs/ssrmisc Jasmin\n\
   -R ../proofs/itrees Jasmin\n\
   -R ../proofs/printing Printing\n\n\
   -Q . \"\"\n"

let pp_coq_project base fnames fmt =
  let modules =
    base :: globs_module_name base :: funnames_module_name base :: fnames
  in
  F.fprintf fmt "%s" coq_project_header;
  pp_newline fmt ();
  List.iter (fun s -> F.fprintf fmt "%s.v\n" s) modules

let makefile =
  "# -*- Makefile -*-\n\n\
   .PHONY: all clean\n\n\
   COQMAKE = $(MAKE) -f Makefile.coq\n\n\
   all: Makefile.coq\n\
   \t+$(COQMAKE)\n\n\
   Makefile.coq: _CoqProject Makefile\n\
   \tcoq_makefile -f _CoqProject -o Makefile.coq\n\n\
   %.vo: Makefile.coq\n\
   \t+$(COQMAKE) $@\n\n\
   clean:\n\
   \t@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi\n\
   \t@find . -type f \\( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o \
   -name '*.glob' -o -name '*.aux' -o -name '*.d' \\) -delete\n\
   \t@rm -f Makefile.coq\n"

let pp_makefile fmt = F.fprintf fmt "%s" makefile

let extract_split arch pp_asm_op (gd, funcs) name base_path =
  let name = rocq_sanitize_s name in
  let base_dir = Filename.dirname base_path in
  let base_module =
    let open Filename in
    remove_extension base_path |> basename |> rocq_sanitize_s
  in
  let make_path m ext = Filename.concat base_dir (m ^ ext) in
  let globs_module = globs_module_name base_module in
  let funnames_module = funnames_module_name base_module in
  let funcs = List.rev funcs in
  let funnames = List.map (fun f -> f.f_name) funcs in
  let fn_modules =
    List.map (fun fd -> (fd, function_module_name base_module fd.f_name)) funcs
  in
  let fn_module_names = List.map snd fn_modules in
  with_out_file (make_path globs_module ".v") (fun fmt ->
      pp_header fmt arch;
      pp_section_ido fmt;
      pp_newline fmt ();
      pp_separator fmt "Globals";
      pp_globs_definition fmt name gd;
      pp_newline fmt ();
      pp_end_ido fmt ());
  with_out_file (make_path funnames_module ".v") (fun fmt ->
      pp_header fmt arch;
      pp_section_ido fmt;
      pp_newline fmt ();
      pp_funnames_block fmt funnames;
      pp_end_ido fmt ());
  List.iter
    (fun (fd, fn_module) ->
      with_out_file (make_path fn_module ".v") (fun fmt ->
          pp_header fmt arch;
          pp_require_import fmt globs_module;
          pp_require_import fmt funnames_module;
          pp_newline fmt ();
          pp_section_ido fmt;
          pp_newline fmt ();
          pp_fd_block pp_asm_op fmt fd;
          pp_newline fmt ();
          pp_end_ido fmt ()))
    fn_modules;
  with_out_file base_path (fun fmt ->
      pp_header fmt arch;
      pp_require_import fmt globs_module;
      pp_require_import fmt funnames_module;
      F.pp_print_list ~pp_sep:pp_print_nothing pp_require_import fmt
        fn_module_names;
      pp_newline fmt ();
      pp_oracles_block fmt;
      pp_prog_block fmt name funcs);
  with_out_file
    (make_path coqproject_name "")
    (pp_coq_project base_module fn_module_names);
  with_out_file (make_path makefile_name "") pp_makefile
