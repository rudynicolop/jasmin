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

(* ABUFLEN____absorb_avx2x4 *)
(* Local variables *)
Definition st_117 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14418).
Definition AT_114 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14419).
Definition buf0_40 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14420).
Definition buf1_40 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14421).
Definition buf2_40 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14422).
Definition buf3_40 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14423).
Definition _TRAILB_66 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14424).
Definition _RATE8_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14425).
Definition offset_177 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14426).
Definition _LEN_110 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14427).
Definition ITERS_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14428).
Definition i_70 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14429).

(* Signature *)
Definition tyin_ABUFLEN____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aint
    ; aint ].
Definition args_ABUFLEN____absorb_avx2x4 : seq var_i :=
  [:: st_117.(gv)
    ; AT_114.(gv)
    ; buf0_40.(gv)
    ; buf1_40.(gv)
    ; buf2_40.(gv)
    ; buf3_40.(gv)
    ; _TRAILB_66.(gv)
    ; _RATE8_54.(gv) ].
Definition tyout_ABUFLEN____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_ABUFLEN____absorb_avx2x4 : seq var_i :=
  [:: st_117.(gv); AT_114.(gv) ].

(* Body *)
Definition body_ABUFLEN____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_177.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_110.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_114) (Pvar _LEN_110)) (Pvar _RATE8_54))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_117.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_177.(gv) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_117
                                                                    ; Pvar AT_114
                                                                    ; Pvar buf0_40
                                                                    ; Pvar buf1_40
                                                                    ; Pvar buf2_40
                                                                    ; Pvar buf3_40
                                                                    ; Pvar offset_177
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_54) (Pvar AT_114)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_110.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_110) (Papp2 (Osub (Op_int)) (Pvar _RATE8_54) (Pvar AT_114))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_114.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_117.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_117 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_54.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_110) (Pvar _RATE8_54)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_70.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_70) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_54)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_117.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_177.(gv) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_117
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_40
                                                                    ; Pvar buf1_40
                                                                    ; Pvar buf2_40
                                                                    ; Pvar buf3_40
                                                                    ; Pvar offset_177
                                                                    ; Pvar _RATE8_54
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_117.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_117 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_70.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_70) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_110.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_110) (Pvar _RATE8_54))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_117.(gv)
                                    ; Lvar AT_114.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_117
                                                                    ; Pvar AT_114
                                                                    ; Pvar buf0_40
                                                                    ; Pvar buf1_40
                                                                    ; Pvar buf2_40
                                                                    ; Pvar buf3_40
                                                                    ; Pvar offset_177
                                                                    ; Pvar _LEN_110
                                                                    ; Pvar _TRAILB_66 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_66) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_117.(gv) ] __addratebit_avx2x4 [:: Pvar st_117
                                                                    ; Pvar _RATE8_54 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____absorb_avx2x4;
    f_params := args_ABUFLEN____absorb_avx2x4;
    f_body := body_ABUFLEN____absorb_avx2x4;
    f_tyout := tyout_ABUFLEN____absorb_avx2x4;
    f_res := res_ABUFLEN____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
