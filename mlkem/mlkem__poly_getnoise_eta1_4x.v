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

(* _poly_getnoise_eta1_4x *)
(* Local variables *)
Definition r0_14101 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14101).
Definition r1_14102 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14102).
Definition r2_14103 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14103).
Definition r3_14104 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14104).
Definition seed_14105 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 14105).
Definition nonce_14106 : gvar :=
  mk_rocq_gvar Slocal (aword U8) (mkident 14106).
Definition buf0_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14107).
Definition buf0_14108 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14108).
Definition buf1_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14109).
Definition buf1_14110 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14110).
Definition buf2_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14111).
Definition buf2_14112 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14112).
Definition buf3_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14113).
Definition buf3_14114 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14114).
Definition nonces_14115 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 4) (mkident 14115).

(* Signature *)
Definition tyin__poly_getnoise_eta1_4x : seq atype :=
  [:: aarr U16 256
    ; aarr U16 256
    ; aarr U16 256
    ; aarr U16 256
    ; aarr U8 32
    ; aword U8 ].
Definition args__poly_getnoise_eta1_4x : seq var_i :=
  [:: r0_14101.(gv)
    ; r1_14102.(gv)
    ; r2_14103.(gv)
    ; r3_14104.(gv)
    ; seed_14105.(gv)
    ; nonce_14106.(gv) ].
Definition tyout__poly_getnoise_eta1_4x : seq atype :=
  [:: aarr U16 256; aarr U16 256; aarr U16 256; aarr U16 256 ].
Definition res__poly_getnoise_eta1_4x : seq var_i :=
  [:: r0_14101.(gv); r1_14102.(gv); r2_14103.(gv); r3_14104.(gv) ].

(* Body *)
Definition body__poly_getnoise_eta1_4x : cmd :=
  [:: cassgn (Lvar buf0_14108.(gv)) (aarr U8 128) (Pvar buf0_s)
    ; cassgn (Lvar buf1_14110.(gv)) (aarr U8 128) (Pvar buf1_s)
    ; cassgn (Lvar buf2_14112.(gv)) (aarr U8 128) (Pvar buf2_s)
    ; cassgn (Lvar buf3_14114.(gv)) (aarr U8 128) (Pvar buf3_s)
    ; copn [::] (Opseudo_op (Ospill Spill [:: aarr U16 256%positive
                                            ; aarr U16 256%positive
                                            ; aarr U16 256%positive
                                            ; aarr U16 256%positive ])) [:: Pvar r0_14101
                                                                    ; Pvar r1_14102
                                                                    ; Pvar r2_14103
                                                                    ; Pvar r3_14104 ]
    ; cassgn (Laset Aligned AAscale U8 nonces_14115.(gv) (Pconst (0)%Z)) (aword U8) (Pvar nonce_14106)
    ; cassgn (Lvar nonce_14106.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_14106) (Papp1 (Oword_of_int U8) (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U8 nonces_14115.(gv) (Pconst (1)%Z)) (aword U8) (Pvar nonce_14106)
    ; cassgn (Lvar nonce_14106.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_14106) (Papp1 (Oword_of_int U8) (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U8 nonces_14115.(gv) (Pconst (2)%Z)) (aword U8) (Pvar nonce_14106)
    ; cassgn (Lvar nonce_14106.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_14106) (Papp1 (Oword_of_int U8) (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U8 nonces_14115.(gv) (Pconst (3)%Z)) (aword U8) (Pvar nonce_14106)
    ; ccall [:: Lvar buf0_14108.(gv)
              ; Lvar buf1_14110.(gv)
              ; Lvar buf2_14112.(gv)
              ; Lvar buf3_14114.(gv) ] _shake256x4_A128__A32_A1 [:: Pvar buf0_14108
                                                                  ; Pvar buf1_14110
                                                                  ; Pvar buf2_14112
                                                                  ; Pvar buf3_14114
                                                                  ; Pvar seed_14105
                                                                  ; Pvar nonces_14115 ]
    ; copn [:: Lnone dummy_var_info (aword U64) ] (Oslh (SLHinit)) [::]
    ; copn [::] (Opseudo_op (Ospill Unspill [:: aarr U16 256%positive
                                              ; aarr U16 256%positive
                                              ; aarr U16 256%positive
                                              ; aarr U16 256%positive ])) [:: Pvar r0_14101
                                                                    ; Pvar r1_14102
                                                                    ; Pvar r2_14103
                                                                    ; Pvar r3_14104 ]
    ; ccall [:: Lvar r0_14101.(gv) ] __poly_cbd_eta1 [:: Pvar r0_14101
                                                       ; Pvar buf0_14108 ]
    ; ccall [:: Lvar r1_14102.(gv) ] __poly_cbd_eta1 [:: Pvar r1_14102
                                                       ; Pvar buf1_14110 ]
    ; ccall [:: Lvar r2_14103.(gv) ] __poly_cbd_eta1 [:: Pvar r2_14103
                                                       ; Pvar buf2_14112 ]
    ; ccall [:: Lvar r3_14104.(gv) ] __poly_cbd_eta1 [:: Pvar r3_14104
                                                       ; Pvar buf3_14114 ] ].

Definition fd__poly_getnoise_eta1_4x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_getnoise_eta1_4x;
    f_params := args__poly_getnoise_eta1_4x;
    f_body := body__poly_getnoise_eta1_4x;
    f_tyout := tyout__poly_getnoise_eta1_4x;
    f_res := res__poly_getnoise_eta1_4x;
    f_extra := tt;
  |}.

End IDO.
