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

(* A1184____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_75 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15996).
Definition AT_72 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15997).
Definition buf_109 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15998).
Definition _TRAILB_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15999).
Definition _RATE8_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16000).
Definition offset_107 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16001).
Definition _LEN_68 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16002).
Definition ITERS_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16003).
Definition i_45 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16004).

(* Signature *)
Definition tyin_A1184____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1184; aint; aint ].
Definition args_A1184____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_75.(gv); AT_72.(gv); buf_109.(gv); _TRAILB_40.(gv); _RATE8_33.(gv) ].
Definition tyout_A1184____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1184____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_75.(gv); AT_72.(gv) ].

(* Body *)
Definition body_A1184____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_107.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_68.(gv)) AT_none (aint) (Pconst (1184)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_72) (Pvar _LEN_68)) (Pvar _RATE8_33))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_75.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_107.(gv) ] A1184____addstate_bcast_avx2x4 [:: Pvar st_75
                                                                    ; Pvar AT_72
                                                                    ; Pvar buf_109
                                                                    ; Pvar offset_107
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_33) (Pvar AT_72)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_68.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_68) (Papp2 (Osub (Op_int)) (Pvar _RATE8_33) (Pvar AT_72))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_72.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_75.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_75 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_33.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_68) (Pvar _RATE8_33)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_45.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_45) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_33)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_75.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_107.(gv) ] A1184____addstate_bcast_avx2x4 [:: Pvar st_75
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_109
                                                                    ; Pvar offset_107
                                                                    ; Pvar _RATE8_33
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_75.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_75 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_45.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_45) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_68.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_68) (Pvar _RATE8_33))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_75.(gv)
                                    ; Lvar AT_72.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1184____addstate_bcast_avx2x4 [:: Pvar st_75
                                                                    ; Pvar AT_72
                                                                    ; Pvar buf_109
                                                                    ; Pvar offset_107
                                                                    ; Pvar _LEN_68
                                                                    ; Pvar _TRAILB_40 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_40) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_75.(gv) ] __addratebit_avx2x4 [:: Pvar st_75
                                                                    ; Pvar _RATE8_33 ]) ]
                              [::]) ].

Definition fd_A1184____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____absorb_bcast_avx2x4;
    f_params := args_A1184____absorb_bcast_avx2x4;
    f_body := body_A1184____absorb_bcast_avx2x4;
    f_tyout := tyout_A1184____absorb_bcast_avx2x4;
    f_res := res_A1184____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
