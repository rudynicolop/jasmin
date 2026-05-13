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

(* __gen_matrix_buf_rejection_filter48 *)
(* Local variables *)
Definition pol : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13853).
Definition counter : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13854).
Definition buf_13855 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13855).
Definition buf_offset : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13856).
Definition load_shuffle : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13857).
Definition mask_13858 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13858).
Definition bounds : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13859).
Definition sst : gvar := mk_rocq_gvar Slocal (aarr U8 2048) (mkident 13860).
Definition ones : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13861).
Definition ms : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13862).
Definition f0_13863 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13863).
Definition f1_13864 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13864).
Definition g0_13865 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13865).
Definition g1_13866 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13866).
Definition good : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13867).
Definition t0_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13868).
Definition shuffle_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13869).
Definition t0_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13870).
Definition shuffle_0_1 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13871).
Definition t1_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13872).
Definition shuffle_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13873).
Definition t1_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13874).
Definition shuffle_1_1 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13875).
Definition shuffle_t : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13876).

(* Signature *)
Definition tyin___gen_matrix_buf_rejection_filter48 : seq atype :=
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
Definition args___gen_matrix_buf_rejection_filter48 : seq var_i :=
  [:: pol.(gv)
    ; counter.(gv)
    ; buf_13855.(gv)
    ; buf_offset.(gv)
    ; load_shuffle.(gv)
    ; mask_13858.(gv)
    ; bounds.(gv)
    ; sst.(gv)
    ; ones.(gv)
    ; ms.(gv) ].
Definition tyout___gen_matrix_buf_rejection_filter48 : seq atype :=
  [:: aarr U16 256; aword U64 ].
Definition res___gen_matrix_buf_rejection_filter48 : seq var_i :=
  [:: pol.(gv); counter.(gv) ].

(* Body *)
Definition body___gen_matrix_buf_rejection_filter48 : cmd :=
  [:: copn [:: Lvar f0_13863.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Unaligned AAdirect U256 buf_13855 (Papp2 (Oadd (Op_int)) (Papp1 (Oint_of_word Unsigned U64) (Pvar buf_offset)) (Pconst (0)%Z))
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (2)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar f1_13864.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Unaligned AAdirect U256 buf_13855 (Papp2 (Oadd (Op_int)) (Papp1 (Oint_of_word Unsigned U64) (Pvar buf_offset)) (Pconst (24)%Z))
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (2)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar f0_13863.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_13863
                                                                    ; Pvar load_shuffle ]
    ; copn [:: Lvar f1_13864.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f1_13864
                                                                    ; Pvar load_shuffle ]
    ; copn [:: Lvar g0_13865.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0_13863
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
    ; copn [:: Lvar g1_13866.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f1_13864
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
    ; copn [:: Lvar f0_13863.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar f0_13863
                                                                    ; Pvar g0_13865
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]
    ; copn [:: Lvar f1_13864.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar f1_13864
                                                                    ; Pvar g1_13866
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]
    ; copn [:: Lvar f0_13863.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_13863
                                                                    ; Pvar mask_13858 ]
    ; copn [:: Lvar f1_13864.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f1_13864
                                                                    ; Pvar mask_13858 ]
    ; copn [:: Lvar g0_13865.(gv) ] (Oasm ((BaseOp ((None), (VPCMPGT VE16 U256))))) [:: Pvar bounds
                                                                    ; Pvar f0_13863 ]
    ; copn [:: Lvar g1_13866.(gv) ] (Oasm ((BaseOp ((None), (VPCMPGT VE16 U256))))) [:: Pvar bounds
                                                                    ; Pvar f1_13864 ]
    ; copn [:: Lvar g0_13865.(gv) ] (Oasm ((BaseOp ((None), (VPACKSS VE16 U256))))) [:: Pvar g0_13865
                                                                    ; Pvar g1_13866 ]
    ; copn [:: Lvar good.(gv) ] (Oasm ((BaseOp ((Some U64), (MOVEMASK VE8 U256))))) [:: Pvar g0_13865 ]
    ; copn [::] (Opseudo_op (Odeclassify (aword U64))) [:: Pvar good ]
    ; copn [:: Lvar good.(gv) ] (Oslh (SLHprotect U64)) [:: Pvar good
                                                          ; Pvar ms ]
    ; cassgn (Lvar t0_0.(gv)) (aword U64) (Pvar good)
    ; cassgn (Lvar t0_0.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t0_0) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_0.(gv) ] (Oasm ((BaseOp ((Some U256), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_0)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t0_0.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_0 ]
    ; cassgn (Lvar t0_0.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_0) (Pvar counter))
    ; cassgn (Lvar t0_1.(gv)) (aword U64) (Pvar good)
    ; cassgn (Lvar t0_1.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar t0_1) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))
    ; cassgn (Lvar t0_1.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t0_1) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_0_1.(gv) ] (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst (Papp1 (Oint_of_word Unsigned U64) (Pvar t0_1)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t0_1.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t0_1 ]
    ; cassgn (Lvar t0_1.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t0_1) (Pvar t0_0))
    ; cassgn (Lvar t1_0.(gv)) (aword U64) (Pvar good)
    ; cassgn (Lvar t1_0.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar t1_0) (Papp1 (Oword_of_int U8) (Pconst (8)%Z)))
    ; cassgn (Lvar t1_0.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t1_0) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_1.(gv) ] (Oasm ((BaseOp ((Some U256), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst (Papp1 (Oint_of_word Unsigned U64) (Pvar t1_0)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t1_0.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t1_0 ]
    ; cassgn (Lvar t1_0.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t1_0) (Pvar t0_1))
    ; cassgn (Lvar t1_1.(gv)) (aword U64) (Pvar good)
    ; cassgn (Lvar t1_1.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar t1_1) (Papp1 (Oword_of_int U8) (Pconst (24)%Z)))
    ; cassgn (Lvar t1_1.(gv)) (aword U64) (Papp2 (Oland U64) (Pvar t1_1) (Papp1 (Oword_of_int U64) (Pconst (255)%Z)))
    ; copn [:: Lvar shuffle_1_1.(gv) ] (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 sst (Papp1 (Oint_of_word Unsigned U64) (Pvar t1_1)) ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar t1_1.(gv) ] (Oasm ((BaseOp ((None), (POPCNT U64))))) [:: Pvar t1_1 ]
    ; cassgn (Lvar t1_1.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar t1_1) (Pvar t1_0))
    ; copn [:: Lvar shuffle_0.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar shuffle_0
                                                                    ; Pvar shuffle_0_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; copn [:: Lvar shuffle_1.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar shuffle_1
                                                                    ; Pvar shuffle_1_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; copn [:: Lvar shuffle_t.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar shuffle_0
                                                                    ; Pvar ones ]
    ; copn [:: Lvar shuffle_0.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKL VE8 U256))))) [:: Pvar shuffle_0
                                                                    ; Pvar shuffle_t ]
    ; copn [:: Lvar shuffle_t.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar shuffle_1
                                                                    ; Pvar ones ]
    ; copn [:: Lvar shuffle_1.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKL VE8 U256))))) [:: Pvar shuffle_1
                                                                    ; Pvar shuffle_t ]
    ; copn [:: Lvar f0_13863.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_13863
                                                                    ; Pvar shuffle_0 ]
    ; copn [:: Lvar f1_13864.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f1_13864
                                                                    ; Pvar shuffle_1 ]
    ; cassgn (Laset Unaligned AAdirect U128 pol.(gv) (Papp1 (Oint_of_word Unsigned U64) (Papp2 (Omul (Op_w U64)) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)) (Pvar counter)))) (aword U128) (Pvar f0_13863)
    ; copn [:: Laset Unaligned AAdirect U128 pol.(gv) (Papp1 (Oint_of_word Unsigned U64) (Papp2 (Omul (Op_w U64)) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)) (Pvar t0_0))) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f0_13863
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; cassgn (Laset Unaligned AAdirect U128 pol.(gv) (Papp1 (Oint_of_word Unsigned U64) (Papp2 (Omul (Op_w U64)) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)) (Pvar t0_1)))) (aword U128) (Pvar f1_13864)
    ; copn [:: Laset Unaligned AAdirect U128 pol.(gv) (Papp1 (Oint_of_word Unsigned U64) (Papp2 (Omul (Op_w U64)) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)) (Pvar t1_0))) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f1_13864
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
    ; cassgn (Lvar counter.(gv)) (aword U64) (Pvar t1_1) ].

Definition fd___gen_matrix_buf_rejection_filter48 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___gen_matrix_buf_rejection_filter48;
    f_params := args___gen_matrix_buf_rejection_filter48;
    f_body := body___gen_matrix_buf_rejection_filter48;
    f_tyout := tyout___gen_matrix_buf_rejection_filter48;
    f_res := res___gen_matrix_buf_rejection_filter48;
    f_extra := tt;
  |}.

End IDO.
