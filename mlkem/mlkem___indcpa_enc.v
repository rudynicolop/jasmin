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

(* __indcpa_enc *)
(* Local variables *)
Definition ct : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13687).
Definition msgp : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13688).
Definition pk_13689 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13689).
Definition noiseseed_13690 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13690).
Definition pkpv_13691 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13691).
Definition w_13692 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13692).
Definition t64_13693 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13693).
Definition publicseed_13694 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13694).
Definition k_13695 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13695).
Definition transposed_13696 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13696).
Definition aat : gvar := mk_rocq_gvar Slocal (aarr U16 2304) (mkident 13697).
Definition nonce_13698 : gvar :=
  mk_rocq_gvar Slocal (aword U8) (mkident 13698).
Definition sp : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13699).
Definition ep : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13700).
Definition epp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13701).
Definition bp_13702 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13702).
Definition v_13703 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13703).

(* Signature *)
Definition tyin___indcpa_enc : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184; aarr U8 32 ].
Definition args___indcpa_enc : seq var_i :=
  [:: ct.(gv); msgp.(gv); pk_13689.(gv); noiseseed_13690.(gv) ].
Definition tyout___indcpa_enc : seq atype := [:: aarr U8 1088 ].
Definition res___indcpa_enc : seq var_i := [:: ct.(gv) ].

(* Body *)
Definition body___indcpa_enc : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 1088%positive ])) [:: Pvar ct ])
    ; MkI dummy_instr_info (Ccall [:: Lvar pkpv_13691.(gv) ] __i_polyvec_frombytes [:: Psub AAscale U8 1152 pk_13689 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cfor
                              (w_13692.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_13693.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 pk_13689 (Papp2 (Omul (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (8)%Z)) (Pvar w_13692)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Odeclassify (aword U64))) [:: Pvar t64_13693 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 publicseed_13694.(gv) (Pvar w_13692)) AT_none (aword U64) (Pvar t64_13693)) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar k_13695.(gv) ] _i_poly_frommsg [:: Pvar k_13695
                                                                    ; Pvar msgp ])
    ; MkI dummy_instr_info (Cassgn (Lvar transposed_13696.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar aat.(gv) ] _gen_matrix_avx2 [:: Pvar aat
                                                                    ; Pvar publicseed_13694
                                                                    ; Pvar transposed_13696 ])
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_13698.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 sp.(gv) (Pconst (0)%Z)
                                    ; Lasub AAscale U16 256 sp.(gv) (Pconst (256)%Z)
                                    ; Lasub AAscale U16 256 sp.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                    ; Lasub AAscale U16 256 ep.(gv) (Pconst (0)%Z) ] _poly_getnoise_eta1_4x [:: Psub AAscale U16 256 sp (Pconst (0)%Z)
                                                                    ; Psub AAscale U16 256 sp (Pconst (256)%Z)
                                                                    ; Psub AAscale U16 256 sp (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                                                    ; Psub AAscale U16 256 ep (Pconst (0)%Z)
                                                                    ; Pvar noiseseed_13690
                                                                    ; Pvar nonce_13698 ])
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_13698.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (4)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 ep.(gv) (Pconst (256)%Z)
                                    ; Lasub AAscale U16 256 ep.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                    ; Lvar epp.(gv)
                                    ; Lasub AAscale U16 256 bp_13702.(gv) (Pconst (0)%Z) ] _poly_getnoise_eta1_4x [:: Psub AAscale U16 256 ep (Pconst (256)%Z)
                                                                    ; Psub AAscale U16 256 ep (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                                                    ; Pvar epp
                                                                    ; Psub AAscale U16 256 bp_13702 (Pconst (0)%Z)
                                                                    ; Pvar noiseseed_13690
                                                                    ; Pvar nonce_13698 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar sp.(gv) ] __polyvec_ntt [:: Pvar sp ])
    ; MkI dummy_instr_info (Cfor
                              (w_13692.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 bp_13702.(gv) (Papp2 (Omul (Op_int)) (Pvar w_13692) (Pconst (256)%Z)) ] __polyvec_pointwise_acc [:: Psub AAscale U16 256 bp_13702 (Papp2 (Omul (Op_int)) (Pvar w_13692) (Pconst (256)%Z))
                                                                    ; Psub AAscale U16 768 aat (Papp2 (Omul (Op_int)) (Pvar w_13692) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z)))
                                                                    ; Pvar sp ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13703.(gv) ] __polyvec_pointwise_acc [:: Pvar v_13703
                                                                    ; Pvar pkpv_13691
                                                                    ; Pvar sp ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bp_13702.(gv) ] __polyvec_invntt [:: Pvar bp_13702 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13703.(gv) ] _poly_invntt [:: Pvar v_13703 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bp_13702.(gv) ] __polyvec_add2 [:: Pvar bp_13702
                                                                    ; Pvar ep ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13703.(gv) ] _poly_add2 [:: Pvar v_13703
                                                                    ; Pvar epp ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13703.(gv) ] _poly_add2 [:: Pvar v_13703
                                                                    ; Pvar k_13695 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bp_13702.(gv) ] __polyvec_reduce [:: Pvar bp_13702 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13703.(gv) ] __poly_reduce [:: Pvar v_13703 ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1088%positive ])) [:: Pvar ct ])
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 960 ct.(gv) (Pconst (0)%Z) ] __i_polyvec_compress [:: Psub AAscale U8 960 ct (Pconst (0)%Z)
                                                                    ; Pvar bp_13702 ])
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 128 ct.(gv) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z))
                                    ; Lvar v_13703.(gv) ] _i_poly_compress [:: Psub AAscale U8 128 ct (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z))
                                                                    ; Pvar v_13703 ]) ].

Definition fd___indcpa_enc : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___indcpa_enc;
    f_params := args___indcpa_enc;
    f_body := body___indcpa_enc;
    f_tyout := tyout___indcpa_enc;
    f_res := res___indcpa_enc;
    f_extra := tt;
  |}.

End IDO.
