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

(* __gen_matrix_buf_rejection_filter24 *)
(* Local variables *)
Definition pol_13805 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13805).
Definition counter_13806 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13806).
Definition buf_13807 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13807).
Definition buf_offset_13808 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13808).
Definition load_shuffle_13809 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13809).
Definition mask_13810 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13810).
Definition bounds_13811 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13811).
Definition sst_13812 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2048) (mkident 13812).
Definition ones_13813 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13813).
Definition ms_13814 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13814).
Definition f0_13815 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13815).
Definition g0_13816 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13816).
Definition g1_13817 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13817).
Definition good_13818 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13818).
Definition t0_0_13819 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13819).
Definition shuffle_0_13820 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13820).
Definition t0_1_13821 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13821).
Definition shuffle_0_1_13822 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13822).
Definition shuffle_t_13823 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13823).
Definition t128_13824 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13824).

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
  [:: pol_13805.(gv)
    ; counter_13806.(gv)
    ; buf_13807.(gv)
    ; buf_offset_13808.(gv)
    ; load_shuffle_13809.(gv)
    ; mask_13810.(gv)
    ; bounds_13811.(gv)
    ; sst_13812.(gv)
    ; ones_13813.(gv)
    ; ms_13814.(gv) ].
Definition tyout___gen_matrix_buf_rejection_filter24 : seq atype :=
  [:: aarr U16 256; aword U64; aword U64 ].
Definition res___gen_matrix_buf_rejection_filter24 : seq var_i :=
  [:: pol_13805.(gv); counter_13806.(gv); ms_13814.(gv) ].

(* Body *)
Definition body___gen_matrix_buf_rejection_filter24 : cmd :=
  [:: copn [:: Lvar f0_13815.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Unaligned AAdirect U256 buf_13807 (Papp2 (Oadd (Op_int)) (Papp1 (Oint_of_word Unsigned U64) (Pvar buf_offset_13808)) (Pconst (0)%Z))
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (2)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar f0_13815.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_13815
                                                                    ; Pvar load_shuffle_13809 ]
    ; copn [:: Lvar g0_13816.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0_13815
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
    ; copn [:: Lvar f0_13815.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar f0_13815
                                                                    ; Pvar g0_13816
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]
    ; copn [:: Lvar f0_13815.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_13815
                                                                    ; Pvar mask_13810 ]
    ; copn [:: Lvar g0_13816.(gv) ] (Oasm ((BaseOp ((None), (VPCMPGT VE16 U256))))) [:: Pvar bounds_13811
                                                                    ; Pvar f0_13815 ]
    ; copn [:: Lvar g1_13817.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
    ; copn [:: Lvar g0_13816.(gv) ] (Oasm ((BaseOp ((None), (VPACKSS VE16 U256))))) [:: Pvar g0_13816
                                                                    ; Pvar g1_13817 ]
    ; copn [:: Lvar good_13818.(gv) ] (Oasm ((BaseOp ((Some U64), (MOVEMASK VE8 U256))))) [:: Pvar g0_13816 ]
    ; copn [::] (Opseudo_op (Odeclassify (aword U64))) [:: Pvar good_13818 ]
    ; copn [:: Lvar good_13818.(gv) ] (Oslh (SLHprotect U64)) [:: Pvar good_13818
                                                                ; Pvar ms_13814 ]
    ; cassgn (Lvar t0_0_13819.(gv)) (aword U64) (Pvar good_13818)
    ; cassgn (Lvar t0_0_13819.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t0_0_13819) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_0_13820.(gv) ] (Oasm ((BaseOp ((Some U256), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst_13812 (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_0_13819)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t0_0_13819.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_0_13819 ]
    ; cassgn (Lvar t0_0_13819.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_0_13819) (Pvar counter_13806))
    ; cassgn (Lvar t0_1_13821.(gv)) (aword U64) (Pvar good_13818)
    ; cassgn (Lvar t0_1_13821.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar t0_1_13821) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))
    ; cassgn (Lvar t0_1_13821.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t0_1_13821) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_0_1_13822.(gv) ] (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst_13812 (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_1_13821)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t0_1_13821.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_1_13821 ]
    ; cassgn (Lvar t0_1_13821.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_1_13821) (Pvar t0_0_13819))
    ; copn [:: Lvar shuffle_0_13820.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar shuffle_0_13820
                                                                    ; Pvar shuffle_0_1_13822
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; copn [:: Lvar shuffle_t_13823.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar shuffle_0_13820
                                                                    ; Pvar ones_13813 ]
    ; copn [:: Lvar shuffle_0_13820.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKL VE8 U256))))) [:: Pvar shuffle_0_13820
                                                                    ; Pvar shuffle_t_13823 ]
    ; copn [:: Lvar f0_13815.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_13815
                                                                    ; Pvar shuffle_0_13820 ]
    ; cassgn (Lvar t128_13824.(gv)) (aword U128) (Pvar f0_13815)
    ; ccall [:: Lvar pol_13805.(gv); Lvar ms_13814.(gv) ] __write_u128_boundchk [:: Pvar pol_13805
                                                                    ; Pvar counter_13806
                                                                    ; Pvar t128_13824
                                                                    ; Pvar ms_13814 ]
    ; copn [:: Lvar t128_13824.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f0_13815
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; ccall [:: Lvar pol_13805.(gv); Lvar ms_13814.(gv) ] __write_u128_boundchk [:: Pvar pol_13805
                                                                    ; Pvar t0_0_13819
                                                                    ; Pvar t128_13824
                                                                    ; Pvar ms_13814 ]
    ; cassgn (Lvar counter_13806.(gv)) (aword U64) (Pvar t0_1_13821) ].

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
