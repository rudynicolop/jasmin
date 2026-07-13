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

(* __gen_matrix_buf_rejection_filter24 *)
(* Local variables *)
Definition pol_1 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13805).
Definition counter_0 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13806).
Definition buf_173 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13807).
Definition buf_offset_0 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13808).
Definition load_shuffle_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13809).
Definition mask_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13810).
Definition bounds_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13811).
Definition sst_0 : gvar := mk_rocq_gvar Slocal (aarr U8 2048) (mkident 13812).
Definition ones_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13813).
Definition ms_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13814).
Definition f0_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13815).
Definition g0_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13816).
Definition g1_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13817).
Definition good_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13818).
Definition t0_0_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13819).
Definition shuffle_0_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13820).
Definition t0_1_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13821).
Definition shuffle_0_1_0 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13822).
Definition shuffle_t_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13823).
Definition t128_25 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 13824).

(* Signature *)
Definition tyin___gen_matrix_buf_rejection_filter24 : seq atype :=
  [:: aarr U16 256
    ; aword U64
    ; aarr U8 536
    ; aword U64
    ; aword U256
    ; aword U256
    ; aword U256
    ; aarr U8 2048
    ; aword U256
    ; aword U64 ].
Definition args___gen_matrix_buf_rejection_filter24 : seq var_i :=
  [:: pol_1.(gv)
    ; counter_0.(gv)
    ; buf_173.(gv)
    ; buf_offset_0.(gv)
    ; load_shuffle_0.(gv)
    ; mask_5.(gv)
    ; bounds_0.(gv)
    ; sst_0.(gv)
    ; ones_0.(gv)
    ; ms_1.(gv) ].
Definition tyout___gen_matrix_buf_rejection_filter24 : seq atype :=
  [:: aarr U16 256; aword U64; aword U64 ].
Definition res___gen_matrix_buf_rejection_filter24 : seq var_i :=
  [:: pol_1.(gv); counter_0.(gv); ms_1.(gv) ].

(* Body *)
Definition body___gen_matrix_buf_rejection_filter24 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar f0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Unaligned AAdirect U256 buf_173 (Papp2 (Oadd (Op_int)) (Papp1 (Oint_of_word Unsigned U64) (Pvar buf_offset_0)) (Pconst (0)%Z))
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar f0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_4
                                                                    ; Pvar load_shuffle_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar g0_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0_4
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar f0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar f0_4
                                                                    ; Pvar g0_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar f0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_4
                                                                    ; Pvar mask_5 ])
    ; MkI dummy_instr_info (Copn [:: Lvar g0_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPCMPGT VE16 U256))))) [:: Pvar bounds_0
                                                                    ; Pvar f0_4 ])
    ; MkI dummy_instr_info (Copn [:: Lvar g1_2.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
    ; MkI dummy_instr_info (Copn [:: Lvar g0_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKSS VE16 U256))))) [:: Pvar g0_2
                                                                    ; Pvar g1_2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar good_0.(gv) ] AT_none (Oasm ((BaseOp ((Some U64), (MOVEMASK VE8 U256))))) [:: Pvar g0_2 ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Odeclassify (aword U64))) [:: Pvar good_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar good_0.(gv) ] AT_none (Oslh (SLHprotect U64)) [:: Pvar good_0
                                                                    ; Pvar ms_1 ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_0_0.(gv)) AT_none (aword U64) (Pvar good_0))
    ; MkI dummy_instr_info (Cassgn (Lvar t0_0_0.(gv)) AT_none (aword U64) (Papp2 (Oland U64) (Pvar t0_0_0) (Papp1 (Oword_of_int U64) (Pconst (255)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar shuffle_0_0.(gv) ] AT_none (Oasm ((BaseOp ((Some U256), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst_0 (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_0_0)) ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar t0_0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_0_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_0_0.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_0_0) (Pvar counter_0)))
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1_0.(gv)) AT_none (aword U64) (Pvar good_0))
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1_0.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar t0_1_0) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1_0.(gv)) AT_none (aword U64) (Papp2 (Oland U64) (Pvar t0_1_0) (Papp1 (Oword_of_int U64) (Pconst (255)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar shuffle_0_1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst_0 (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_1_0)) ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar t0_1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_1_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1_0.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_1_0) (Pvar t0_0_0)))
    ; MkI dummy_instr_info (Copn [:: Lvar shuffle_0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar shuffle_0_0
                                                                    ; Pvar shuffle_0_1_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar shuffle_t_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar shuffle_0_0
                                                                    ; Pvar ones_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar shuffle_0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE8 U256))))) [:: Pvar shuffle_0_0
                                                                    ; Pvar shuffle_t_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar f0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_4
                                                                    ; Pvar shuffle_0_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar t128_25.(gv)) AT_none (aword U128) (Pvar f0_4))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_1.(gv); Lvar ms_1.(gv) ] __write_u128_boundchk [:: Pvar pol_1
                                                                    ; Pvar counter_0
                                                                    ; Pvar t128_25
                                                                    ; Pvar ms_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t128_25.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f0_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_1.(gv); Lvar ms_1.(gv) ] __write_u128_boundchk [:: Pvar pol_1
                                                                    ; Pvar t0_0_0
                                                                    ; Pvar t128_25
                                                                    ; Pvar ms_1 ])
    ; MkI dummy_instr_info (Cassgn (Lvar counter_0.(gv)) AT_none (aword U64) (Pvar t0_1_0)) ].

Definition fd___gen_matrix_buf_rejection_filter24 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___gen_matrix_buf_rejection_filter24;
    f_params := args___gen_matrix_buf_rejection_filter24;
    f_body := body___gen_matrix_buf_rejection_filter24;
    f_tyout := tyout___gen_matrix_buf_rejection_filter24;
    f_res := res___gen_matrix_buf_rejection_filter24;
    f_extra := tt;
  |}.

End IDO.
