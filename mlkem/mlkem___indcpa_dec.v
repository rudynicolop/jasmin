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

(* __indcpa_dec *)
(* Local variables *)
Definition msgp_0 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13675).
Definition ct_0 : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13676).
Definition sk_0 : gvar := mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13677).
Definition bp_3 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13678).
Definition v_2 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13679).
Definition skpv_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13680).
Definition t_18 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13681).
Definition mp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13682).

(* Signature *)
Definition tyin___indcpa_dec : seq atype :=
  [:: aarr U8 32; aarr U8 1088; aarr U8 1152 ].
Definition args___indcpa_dec : seq var_i :=
  [:: msgp_0.(gv); ct_0.(gv); sk_0.(gv) ].
Definition tyout___indcpa_dec : seq atype := [:: aarr U8 32 ].
Definition res___indcpa_dec : seq var_i := [:: msgp_0.(gv) ].

(* Body *)
Definition body___indcpa_dec : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar bp_3.(gv) ] __i_polyvec_decompress [:: Pvar ct_0 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_2.(gv) ] _i_poly_decompress [:: Pvar v_2
                                                                    ; Psub AAscale U8 128 ct_0 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar skpv_0.(gv) ] __i_polyvec_frombytes [:: Pvar sk_0 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bp_3.(gv) ] __polyvec_ntt [:: Pvar bp_3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar t_18.(gv) ] __polyvec_pointwise_acc [:: Pvar t_18
                                                                    ; Pvar skpv_0
                                                                    ; Pvar bp_3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar t_18.(gv) ] _poly_invntt [:: Pvar t_18 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar mp.(gv) ] _poly_sub [:: Pvar mp
                                                                 ; Pvar v_2
                                                                 ; Pvar t_18 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar mp.(gv) ] __poly_reduce [:: Pvar mp ])
    ; MkI dummy_instr_info (Ccall [:: Lvar msgp_0.(gv); Lvar mp.(gv) ] _i_poly_tomsg [:: Pvar msgp_0
                                                                    ; Pvar mp ]) ].

Definition fd___indcpa_dec : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___indcpa_dec;
    f_params := args___indcpa_dec;
    f_body := body___indcpa_dec;
    f_tyout := tyout___indcpa_dec;
    f_res := res___indcpa_dec;
    f_extra := tt;
  |}.

End IDO.
