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

(* __indcpa_keypair *)
(* Local variables *)
Definition pk : gvar := mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13709).
Definition sk : gvar := mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13710).
Definition randomnessp : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13711).
Definition i_98 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13712).
Definition t64_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13713).
Definition inbuf : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 13714).
Definition buf_179 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13715).
Definition publicseed : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13716).
Definition noiseseed : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13717).
Definition transposed_1 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13718).
Definition aa : gvar := mk_rocq_gvar Slocal (aarr U16 2304) (mkident 13719).
Definition nonce_2 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 13720).
Definition skpv : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13721).
Definition e_2 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13722).
Definition pkpv : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13723).

(* Signature *)
Definition tyin___indcpa_keypair : seq atype :=
  [:: aarr U8 1184; aarr U8 1152; aarr U8 32 ].
Definition args___indcpa_keypair : seq var_i :=
  [:: pk.(gv); sk.(gv); randomnessp.(gv) ].
Definition tyout___indcpa_keypair : seq atype :=
  [:: aarr U8 1184; aarr U8 1152 ].
Definition res___indcpa_keypair : seq var_i := [:: pk.(gv); sk.(gv) ].

(* Body *)
Definition body___indcpa_keypair : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 1184%positive
                                                                    ; aarr U8 1152%positive ])) [:: Pvar pk
                                                                    ; Pvar sk ])
    ; MkI dummy_instr_info (Cfor
                              (i_98.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_13.(gv)) AT_none (aword U64) (Pget Unaligned AAscale U64 randomnessp (Pvar i_98)))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 inbuf.(gv) (Pvar i_98)) AT_none (aword U64) (Pvar t64_13)) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 inbuf.(gv) (Pconst (32)%Z)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (3)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_179.(gv) ] _sha3_512A_A33 [:: Pvar buf_179
                                                                    ; Pvar inbuf ])
    ; MkI dummy_instr_info (Cfor
                              (i_98.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_13.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 buf_179 (Pvar i_98)))
                                ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Odeclassify (aword U64))) [:: Pvar t64_13 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 publicseed.(gv) (Pvar i_98)) AT_none (aword U64) (Pvar t64_13))
                                ; MkI dummy_instr_info (Cassgn (Lvar t64_13.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 buf_179 (Papp2 (Oadd (Op_int)) (Pvar i_98) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 noiseseed.(gv) (Pvar i_98)) AT_none (aword U64) (Pvar t64_13)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar transposed_1.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar aa.(gv) ] _gen_matrix_avx2 [:: Pvar aa
                                                                    ; Pvar publicseed
                                                                    ; Pvar transposed_1 ])
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_2.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 skpv.(gv) (Pconst (0)%Z)
                                    ; Lasub AAscale U16 256 skpv.(gv) (Pconst (256)%Z)
                                    ; Lasub AAscale U16 256 skpv.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                    ; Lasub AAscale U16 256 e_2.(gv) (Pconst (0)%Z) ] _poly_getnoise_eta1_4x [:: Psub AAscale U16 256 skpv (Pconst (0)%Z)
                                                                    ; Psub AAscale U16 256 skpv (Pconst (256)%Z)
                                                                    ; Psub AAscale U16 256 skpv (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                                                    ; Psub AAscale U16 256 e_2 (Pconst (0)%Z)
                                                                    ; Pvar noiseseed
                                                                    ; Pvar nonce_2 ])
    ; MkI dummy_instr_info (Cassgn (Lvar nonce_2.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (4)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 e_2.(gv) (Pconst (256)%Z)
                                    ; Lasub AAscale U16 256 e_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                    ; Lasub AAscale U16 256 pkpv.(gv) (Pconst (0)%Z)
                                    ; Lasub AAscale U16 256 pkpv.(gv) (Pconst (256)%Z) ] _poly_getnoise_eta1_4x [:: Psub AAscale U16 256 e_2 (Pconst (256)%Z)
                                                                    ; Psub AAscale U16 256 e_2 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))
                                                                    ; Psub AAscale U16 256 pkpv (Pconst (0)%Z)
                                                                    ; Psub AAscale U16 256 pkpv (Pconst (256)%Z)
                                                                    ; Pvar noiseseed
                                                                    ; Pvar nonce_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar skpv.(gv) ] __polyvec_ntt [:: Pvar skpv ])
    ; MkI dummy_instr_info (Ccall [:: Lvar e_2.(gv) ] __polyvec_ntt [:: Pvar e_2 ])
    ; MkI dummy_instr_info (Cfor
                              (i_98.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 pkpv.(gv) (Papp2 (Omul (Op_int)) (Pvar i_98) (Pconst (256)%Z)) ] __polyvec_pointwise_acc [:: Psub AAscale U16 256 pkpv (Papp2 (Omul (Op_int)) (Pvar i_98) (Pconst (256)%Z))
                                                                    ; Psub AAscale U16 768 aa (Papp2 (Omul (Op_int)) (Pvar i_98) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z)))
                                                                    ; Pvar skpv ])
                                ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 pkpv.(gv) (Papp2 (Omul (Op_int)) (Pvar i_98) (Pconst (256)%Z)) ] _poly_frommont [:: Psub AAscale U16 256 pkpv (Papp2 (Omul (Op_int)) (Pvar i_98) (Pconst (256)%Z)) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar pkpv.(gv) ] __polyvec_add2 [:: Pvar pkpv
                                                                    ; Pvar e_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar pkpv.(gv) ] __polyvec_reduce [:: Pvar pkpv ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1184%positive
                                                                    ; aarr U8 1152%positive ])) [:: Pvar pk
                                                                    ; Pvar sk ])
    ; MkI dummy_instr_info (Ccall [:: Lvar sk.(gv) ] __i_polyvec_tobytes [:: Pvar sk
                                                                    ; Pvar skpv ])
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 1152 pk.(gv) (Pconst (0)%Z) ] __i_polyvec_tobytes [:: Psub AAscale U8 1152 pk (Pconst (0)%Z)
                                                                    ; Pvar pkpv ])
    ; MkI dummy_instr_info (Cfor
                              (i_98.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_13.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 publicseed (Pvar i_98)))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 pk.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Oadd (Op_int)) (Pvar i_98) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (8)%Z))) (Pconst (8)%Z))) AT_none (aword U64) (Pvar t64_13)) ]) ].

Definition fd___indcpa_keypair : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___indcpa_keypair;
    f_params := args___indcpa_keypair;
    f_body := body___indcpa_keypair;
    f_tyout := tyout___indcpa_keypair;
    f_res := res___indcpa_keypair;
    f_extra := tt;
  |}.

End IDO.
