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
Definition st_17405 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17405).
Definition AT_17406 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17406).
Definition buf_17407 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17407).
Definition offset_17408 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17408).
Definition _LEN_17409 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17409).
Definition _TRAILB_17410 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17410).
Definition DELTA_17411 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17411).
Definition AT8_17412 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17412).
Definition w_17413 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17413).
Definition j_at_17414 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17414).

(* Signature *)
Definition tyin_A32____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 32; aword U64; aint; aint ].
Definition args_A32____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17405.(gv)
    ; AT_17406.(gv)
    ; buf_17407.(gv)
    ; offset_17408.(gv)
    ; _LEN_17409.(gv)
    ; _TRAILB_17410.(gv) ].
Definition tyout_A32____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A32____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17405.(gv); AT_17406.(gv); offset_17408.(gv) ].

(* Body *)
Definition body_A32____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17411.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_17412.(gv)) AT_none (aint) (Pvar AT_17406))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17406.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17406) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17412) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17411.(gv)
                                                                ; Lvar _LEN_17409.(gv)
                                                                ; Lvar _TRAILB_17410.(gv)
                                                                ; Lvar AT8_17412.(gv)
                                                                ; Lvar w_17413.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_17407
                                                                    ; Pvar offset_17408
                                                                    ; Pvar DELTA_17411
                                                                    ; Pvar _LEN_17409
                                                                    ; Pvar _TRAILB_17410
                                                                    ; Pvar AT_17406
                                                                    ; Pvar AT8_17412 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17413.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17413) (Pget Aligned AAscale U256 st_17405 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17406) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17405.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17406) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_17413))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17406.(gv)) AT_none (aint) (Pvar AT8_17412)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17408.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17408) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17411))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_17414.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17406) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17414) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17406) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17409) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_17413.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17407 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17408)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17408.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17408) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17413.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17413) (Pget Unaligned AAdirect U256 st_17405 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17414)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_17405.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17414))) AT_none (aword U256) (Pvar w_17413))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_17414.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17414) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17406.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17406) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17409) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17409.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17409) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17409)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_17410) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17411.(gv)
                                                                ; Lvar _LEN_17409.(gv)
                                                                ; Lvar _TRAILB_17410.(gv)
                                                                ; Lvar AT_17406.(gv)
                                                                ; Lvar w_17413.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_17407
                                                                    ; Pvar offset_17408
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17409
                                                                    ; Pvar _TRAILB_17410
                                                                    ; Pvar AT_17406
                                                                    ; Pvar AT_17406 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17413.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17413) (Pget Unaligned AAdirect U256 st_17405 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17414)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_17405.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17414))) AT_none (aword U256) (Pvar w_17413))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17408.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17408) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17411)))) ]
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
