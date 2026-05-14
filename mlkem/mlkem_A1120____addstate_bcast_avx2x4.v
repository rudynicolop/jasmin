From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A1120____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_15248 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15248).
Definition AT_15249 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15249).
Definition buf_15250 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15250).
Definition offset_15251 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15251).
Definition _LEN_15252 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15252).
Definition _TRAILB_15253 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15253).
Definition DELTA_15254 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15254).
Definition AT8_15255 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15255).
Definition w_15256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15256).
Definition j_at_15257 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15257).

(* Signature *)
Definition tyin_A1120____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1120; aword U64; aint; aint ].
Definition args_A1120____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_15248.(gv)
    ; AT_15249.(gv)
    ; buf_15250.(gv)
    ; offset_15251.(gv)
    ; _LEN_15252.(gv)
    ; _TRAILB_15253.(gv) ].
Definition tyout_A1120____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1120____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_15248.(gv); AT_15249.(gv); offset_15251.(gv) ].

(* Body *)
Definition body_A1120____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15254.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_15255.(gv)) AT_none (aint) (Pvar AT_15249))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15249.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15249) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_15255) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_15254.(gv)
                                                                ; Lvar _LEN_15252.(gv)
                                                                ; Lvar _TRAILB_15253.(gv)
                                                                ; Lvar AT8_15255.(gv)
                                                                ; Lvar w_15256.(gv) ] A1120____a_ilen_read_bcast_upto8_at [:: Pvar buf_15250
                                                                    ; Pvar offset_15251
                                                                    ; Pvar DELTA_15254
                                                                    ; Pvar _LEN_15252
                                                                    ; Pvar _TRAILB_15253
                                                                    ; Pvar AT_15249
                                                                    ; Pvar AT8_15255 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_15256.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_15256) (Pget Aligned AAscale U256 st_15248 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15249) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_15248.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15249) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_15256))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15249.(gv)) AT_none (aint) (Pvar AT8_15255)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15251.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15251) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15254))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_15257.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15249) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_15257) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15249) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15252) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_15256.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_15250 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15251)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15251.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15251) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_15256.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_15256) (Pget Unaligned AAdirect U256 st_15248 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_15257)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_15248.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_15257))) AT_none (aword U256) (Pvar w_15256))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_15257.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15257) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15249.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_15249) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15252) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15252.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15252) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15252)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_15253) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_15254.(gv)
                                                                ; Lvar _LEN_15252.(gv)
                                                                ; Lvar _TRAILB_15253.(gv)
                                                                ; Lvar AT_15249.(gv)
                                                                ; Lvar w_15256.(gv) ] A1120____a_ilen_read_bcast_upto8_at [:: Pvar buf_15250
                                                                    ; Pvar offset_15251
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15252
                                                                    ; Pvar _TRAILB_15253
                                                                    ; Pvar AT_15249
                                                                    ; Pvar AT_15249 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_15256.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_15256) (Pget Unaligned AAdirect U256 st_15248 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_15257)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_15248.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_15257))) AT_none (aword U256) (Pvar w_15256))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15251.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15251) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15254)))) ]
                              [::]) ].

Definition fd_A1120____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____addstate_bcast_avx2x4;
    f_params := args_A1120____addstate_bcast_avx2x4;
    f_body := body_A1120____addstate_bcast_avx2x4;
    f_tyout := tyout_A1120____addstate_bcast_avx2x4;
    f_res := res_A1120____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
