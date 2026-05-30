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

(* _poly_getnoise_eta1_4x *)
(* Local variables *)
Definition r0_16 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14101).
Definition r1_16 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14102).
Definition r2_13 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14103).
Definition r3_16 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14104).
Definition seed_4 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14105).
Definition nonce_1 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14106).
Definition buf0_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14107).
Definition buf0_44 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14108).
Definition buf1_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14109).
Definition buf1_44 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14110).
Definition buf2_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14111).
Definition buf2_44 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14112).
Definition buf3_s : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14113).
Definition buf3_44 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14114).
Definition nonces_0 : gvar := mk_rocq_gvar Slocal (aarr U8 4) (mkident 14115).

(* Signature *)
Definition tyin__poly_getnoise_eta1_4x : seq atype :=
  [:: aarr U16 256
    ; aarr U16 256
    ; aarr U16 256
    ; aarr U16 256
    ; aarr U8 32
    ; aword U8 ].
Definition args__poly_getnoise_eta1_4x : seq var_i :=
  [:: r0_16.(gv)
    ; r1_16.(gv)
    ; r2_13.(gv)
    ; r3_16.(gv)
    ; seed_4.(gv)
    ; nonce_1.(gv) ].
Definition tyout__poly_getnoise_eta1_4x : seq atype :=
  [:: aarr U16 256; aarr U16 256; aarr U16 256; aarr U16 256 ].
Definition res__poly_getnoise_eta1_4x : seq var_i :=
  [:: r0_16.(gv); r1_16.(gv); r2_13.(gv); r3_16.(gv) ].

(* Body *)
Definition body__poly_getnoise_eta1_4x : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar buf0_44.(gv)) AT_none (aarr U8 128) (Pvar buf0_s))
    ; MkI dummy_instr_info (Cassgn (Lvar buf1_44.(gv)) AT_none (aarr U8 128) (Pvar buf1_s))
    ; MkI dummy_instr_info (Cassgn (Lvar buf2_44.(gv)) AT_none (aarr U8 128) (Pvar buf2_s))
    ; MkI dummy_instr_info (Cassgn (Lvar buf3_44.(gv)) AT_none (aarr U8 128) (Pvar buf3_s))
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U16 256%positive
                                                                    ; aarr U16 256%positive
                                                                    ; aarr U16 256%positive
                                                                    ; aarr U16 256%positive ])) [:: Pvar r0_16
                                                                    ; Pvar r1_16
                                                                    ; Pvar r2_13
                                                                    ; Pvar r3_16 ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 nonces_0.(gv) (Pconst (0)%Z)) AT_none (aword U8) (Pvar nonce_1))
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_1.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_1) (Papp1 (Oword_of_int U8) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 nonces_0.(gv) (Pconst (1)%Z)) AT_none (aword U8) (Pvar nonce_1))
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_1.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_1) (Papp1 (Oword_of_int U8) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 nonces_0.(gv) (Pconst (2)%Z)) AT_none (aword U8) (Pvar nonce_1))
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_1.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar nonce_1) (Papp1 (Oword_of_int U8) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 nonces_0.(gv) (Pconst (3)%Z)) AT_none (aword U8) (Pvar nonce_1))
    ; MkI dummy_instr_info (Ccall [:: Lvar buf0_44.(gv)
                                    ; Lvar buf1_44.(gv)
                                    ; Lvar buf2_44.(gv)
                                    ; Lvar buf3_44.(gv) ] _shake256x4_A128__A32_A1 [:: Pvar buf0_44
                                                                    ; Pvar buf1_44
                                                                    ; Pvar buf2_44
                                                                    ; Pvar buf3_44
                                                                    ; Pvar seed_4
                                                                    ; Pvar nonces_0 ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U16 256%positive
                                                                    ; aarr U16 256%positive
                                                                    ; aarr U16 256%positive
                                                                    ; aarr U16 256%positive ])) [:: Pvar r0_16
                                                                    ; Pvar r1_16
                                                                    ; Pvar r2_13
                                                                    ; Pvar r3_16 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_16.(gv) ] __poly_cbd_eta1 [:: Pvar r0_16
                                                                    ; Pvar buf0_44 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r1_16.(gv) ] __poly_cbd_eta1 [:: Pvar r1_16
                                                                    ; Pvar buf1_44 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r2_13.(gv) ] __poly_cbd_eta1 [:: Pvar r2_13
                                                                    ; Pvar buf2_44 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r3_16.(gv) ] __poly_cbd_eta1 [:: Pvar r3_16
                                                                    ; Pvar buf3_44 ]) ].

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
