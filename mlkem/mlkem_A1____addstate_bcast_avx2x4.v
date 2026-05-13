From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A1____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_18169 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18169).
Definition AT_18170 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18170).
Definition buf_18171 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18171).
Definition offset_18172 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18172).
Definition _LEN_18173 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18173).
Definition _TRAILB_18174 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18174).
Definition DELTA_18175 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18175).
Definition AT8_18176 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18176).
Definition w_18177 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18177).
Definition j_at_18178 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18178).

(* Signature *)
Definition tyin_A1____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1; aword U64; aint; aint ].
Definition args_A1____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_18169.(gv)
    ; AT_18170.(gv)
    ; buf_18171.(gv)
    ; offset_18172.(gv)
    ; _LEN_18173.(gv)
    ; _TRAILB_18174.(gv) ].
Definition tyout_A1____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_18169.(gv); AT_18170.(gv); offset_18172.(gv) ].

(* Body *)
Definition body_A1____addstate_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_18175.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_18176.(gv)) (aint) (Pvar AT_18170)
    ; cassgn (Lvar AT_18170.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18170) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_18176) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar DELTA_18175.(gv)
                    ; Lvar _LEN_18173.(gv)
                    ; Lvar _TRAILB_18174.(gv)
                    ; Lvar AT8_18176.(gv)
                    ; Lvar w_18177.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_18171
                                                                    ; Pvar offset_18172
                                                                    ; Pvar DELTA_18175
                                                                    ; Pvar _LEN_18173
                                                                    ; Pvar _TRAILB_18174
                                                                    ; Pvar AT_18170
                                                                    ; Pvar AT8_18176 ]
          ; cassgn (Lvar w_18177.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18177) (Pget Aligned AAscale U256 st_18169 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18170) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_18169.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18170) (Pconst (8)%Z))) (aword U256) (Pvar w_18177)
          ; cassgn (Lvar AT_18170.(gv)) (aint) (Pvar AT8_18176) ]
        [::]
    ; cassgn (Lvar offset_18172.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18172) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18175)))
    ; cassgn (Lvar j_at_18178.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18170) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_18178) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18170) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18173) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_18177.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_18171 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18172)) ]
          ; cassgn (Lvar offset_18172.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18172) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_18177.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18177) (Pget Unaligned AAdirect U256 st_18169 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_18178))))
          ; cassgn (Laset Unaligned AAdirect U256 st_18169.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_18178))) (aword U256) (Pvar w_18177)
          ; cassgn (Lvar j_at_18178.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18178) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_18170.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_18170) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18173) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_18173.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18173) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18173)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_18174) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_18175.(gv)
                    ; Lvar _LEN_18173.(gv)
                    ; Lvar _TRAILB_18174.(gv)
                    ; Lvar AT_18170.(gv)
                    ; Lvar w_18177.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_18171
                                                                    ; Pvar offset_18172
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_18173
                                                                    ; Pvar _TRAILB_18174
                                                                    ; Pvar AT_18170
                                                                    ; Pvar AT_18170 ]
          ; cassgn (Lvar w_18177.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18177) (Pget Unaligned AAdirect U256 st_18169 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_18178))))
          ; cassgn (Laset Unaligned AAdirect U256 st_18169.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_18178))) (aword U256) (Pvar w_18177)
          ; cassgn (Lvar offset_18172.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18172) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18175))) ]
        [::] ].

Definition fd_A1____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____addstate_bcast_avx2x4;
    f_params := args_A1____addstate_bcast_avx2x4;
    f_body := body_A1____addstate_bcast_avx2x4;
    f_tyout := tyout_A1____addstate_bcast_avx2x4;
    f_res := res_A1____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
