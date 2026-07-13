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

(* A32____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_40 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17405).
Definition AT_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17406).
Definition buf_54 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17407).
Definition offset_44 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17408).
Definition _LEN_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17409).
Definition _TRAILB_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17410).
Definition DELTA_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17411).
Definition AT8_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17412).
Definition w_37 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17413).
Definition j_at_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17414).

(* Signature *)
Definition tyin_A32____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 32; aword U64; aint; aint ].
Definition args_A32____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_40.(gv)
    ; AT_35.(gv)
    ; buf_54.(gv)
    ; offset_44.(gv)
    ; _LEN_33.(gv)
    ; _TRAILB_19.(gv) ].
Definition tyout_A32____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A32____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_40.(gv); AT_35.(gv); offset_44.(gv) ].

(* Body *)
Definition body_A32____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_30.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_13.(gv)) AT_none (aint) (Pvar AT_35))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_35.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_35) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_13) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_30.(gv)
                                                                ; Lvar _LEN_33.(gv)
                                                                ; Lvar _TRAILB_19.(gv)
                                                                ; Lvar AT8_13.(gv)
                                                                ; Lvar w_37.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_54
                                                                    ; Pvar offset_44
                                                                    ; Pvar DELTA_30
                                                                    ; Pvar _LEN_33
                                                                    ; Pvar _TRAILB_19
                                                                    ; Pvar AT_35
                                                                    ; Pvar AT8_13 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_37.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_37) (Pget Aligned AAscale U256 st_40 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_35) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_40.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_35) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_37))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_35.(gv)) AT_none (aint) (Pvar AT8_13)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_44.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_44) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_30))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_5.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_35) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_5) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_35) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_33) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_37.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_54 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_44)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_44.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_44) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_37.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_37) (Pget Unaligned AAdirect U256 st_40 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_5)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_40.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_5))) AT_none (aword U256) (Pvar w_37))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_5.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_5) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_35.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_35) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_33) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_33.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_33) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_33)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_19) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_30.(gv)
                                                                ; Lvar _LEN_33.(gv)
                                                                ; Lvar _TRAILB_19.(gv)
                                                                ; Lvar AT_35.(gv)
                                                                ; Lvar w_37.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_54
                                                                    ; Pvar offset_44
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_33
                                                                    ; Pvar _TRAILB_19
                                                                    ; Pvar AT_35
                                                                    ; Pvar AT_35 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_37.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_37) (Pget Unaligned AAdirect U256 st_40 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_5)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_40.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_5))) AT_none (aword U256) (Pvar w_37))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_44.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_44) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_30)))) ]
                              [::]) ].

Definition fd_A32____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____addstate_bcast_avx2x4;
    f_params := args_A32____addstate_bcast_avx2x4;
    f_body := body_A32____addstate_bcast_avx2x4;
    f_tyout := tyout_A32____addstate_bcast_avx2x4;
    f_res := res_A32____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
