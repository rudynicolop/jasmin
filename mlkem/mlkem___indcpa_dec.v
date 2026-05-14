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
Definition msgp_13675 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13675).
Definition ct_13676 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13676).
Definition sk_13677 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13677).
Definition bp_13678 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13678).
Definition v_13679 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13679).
Definition skpv_13680 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13680).
Definition t_13681 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13681).
Definition mp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13682).

(* Signature *)
Definition tyin___indcpa_dec : seq atype :=
  [:: aarr U8 32; aarr U8 1088; aarr U8 1152 ].
Definition args___indcpa_dec : seq var_i :=
  [:: msgp_13675.(gv); ct_13676.(gv); sk_13677.(gv) ].
Definition tyout___indcpa_dec : seq atype := [:: aarr U8 32 ].
Definition res___indcpa_dec : seq var_i := [:: msgp_13675.(gv) ].

(* Body *)
Definition body___indcpa_dec : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar bp_13678.(gv) ] __i_polyvec_decompress [:: Pvar ct_13676 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar v_13679.(gv) ] _i_poly_decompress [:: Pvar v_13679
                                                                    ; Psub AAscale U8 128 ct_13676 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar skpv_13680.(gv) ] __i_polyvec_frombytes [:: Pvar sk_13677 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bp_13678.(gv) ] __polyvec_ntt [:: Pvar bp_13678 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar t_13681.(gv) ] __polyvec_pointwise_acc [:: Pvar t_13681
                                                                    ; Pvar skpv_13680
                                                                    ; Pvar bp_13678 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar t_13681.(gv) ] _poly_invntt [:: Pvar t_13681 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar mp.(gv) ] _poly_sub [:: Pvar mp
                                                                 ; Pvar v_13679
                                                                 ; Pvar t_13681 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar mp.(gv) ] __poly_reduce [:: Pvar mp ])
    ; MkI dummy_instr_info (Ccall [:: Lvar msgp_13675.(gv); Lvar mp.(gv) ] _i_poly_tomsg [:: Pvar msgp_13675
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
