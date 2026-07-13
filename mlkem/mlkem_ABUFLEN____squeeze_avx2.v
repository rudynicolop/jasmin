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

(* ABUFLEN____squeeze_avx2 *)
(* Local variables *)
Definition st_113 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14503).
Definition buf_163 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14504).
Definition _RATE8_52 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14505).
Definition offset_173 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14506).
Definition _LEN_106 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14507).
Definition ITERS_52 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14508).
Definition LO_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14509).
Definition i_68 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14510).

(* Signature *)
Definition tyin_ABUFLEN____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 536; aint ].
Definition args_ABUFLEN____squeeze_avx2 : seq var_i :=
  [:: st_113.(gv); buf_163.(gv); _RATE8_52.(gv) ].
Definition tyout_ABUFLEN____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 536 ].
Definition res_ABUFLEN____squeeze_avx2 : seq var_i :=
  [:: st_113.(gv); buf_163.(gv) ].

(* Body *)
Definition body_ABUFLEN____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_173.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_106.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_52.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_106) (Pvar _RATE8_52)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_20.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_106) (Pvar _RATE8_52)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_68.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_68) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_52)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_113.(gv) ] _keccakf1600_avx2 [:: Pvar st_113 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_163.(gv)
                                                                ; Lvar offset_173.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_163
                                                                    ; Pvar offset_173
                                                                    ; Pvar _RATE8_52
                                                                    ; Pvar st_113 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_68.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_68) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_20))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_113.(gv) ] _keccakf1600_avx2 [:: Pvar st_113 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_163.(gv)
                                                                ; Lvar offset_173.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_163
                                                                    ; Pvar offset_173
                                                                    ; Pvar LO_20
                                                                    ; Pvar st_113 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____squeeze_avx2;
    f_params := args_ABUFLEN____squeeze_avx2;
    f_body := body_ABUFLEN____squeeze_avx2;
    f_tyout := tyout_ABUFLEN____squeeze_avx2;
    f_res := res_ABUFLEN____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
