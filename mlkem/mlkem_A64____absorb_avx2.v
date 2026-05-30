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

(* A64____absorb_avx2 *)
(* Local variables *)
Definition st_57 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16692).
Definition AT_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16693).
Definition buf_79 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16694).
Definition _TRAILB_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16695).
Definition _RATE8_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16696).
Definition offset_75 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16697).
Definition _LEN_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16698).
Definition ITERS_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16699).
Definition i_35 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16700).

(* Signature *)
Definition tyin_A64____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 64; aint; aint ].
Definition args_A64____absorb_avx2 : seq var_i :=
  [:: st_57.(gv); AT_54.(gv); buf_79.(gv); _TRAILB_30.(gv); _RATE8_24.(gv) ].
Definition tyout_A64____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A64____absorb_avx2 : seq var_i := [:: st_57.(gv); AT_54.(gv) ].

(* Body *)
Definition body_A64____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_75.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_50.(gv)) AT_none (aint) (Pconst (64)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_54) (Pvar _LEN_50)) (Pvar _RATE8_24))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_57.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_75.(gv) ] A64____addstate_avx2 [:: Pvar st_57
                                                                    ; Pvar AT_54
                                                                    ; Pvar buf_79
                                                                    ; Pvar offset_75
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_24) (Pvar AT_54)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_50.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_50) (Papp2 (Osub (Op_int)) (Pvar _RATE8_24) (Pvar AT_54))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_54.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_57.(gv) ] _keccakf1600_avx2 [:: Pvar st_57 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_24.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_50) (Pvar _RATE8_24)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_35.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_35) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_24)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_57.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_75.(gv) ] A64____addstate_avx2 [:: Pvar st_57
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_79
                                                                    ; Pvar offset_75
                                                                    ; Pvar _RATE8_24
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_57.(gv) ] _keccakf1600_avx2 [:: Pvar st_57 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_35.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_35) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_50.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_50) (Pvar _RATE8_24))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_57.(gv)
                                    ; Lvar AT_54.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A64____addstate_avx2 [:: Pvar st_57
                                                                    ; Pvar AT_54
                                                                    ; Pvar buf_79
                                                                    ; Pvar offset_75
                                                                    ; Pvar _LEN_50
                                                                    ; Pvar _TRAILB_30 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_30) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_57.(gv) ] __addratebit_avx2 [:: Pvar st_57
                                                                    ; Pvar _RATE8_24 ]) ]
                              [::]) ].

Definition fd_A64____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____absorb_avx2;
    f_params := args_A64____absorb_avx2;
    f_body := body_A64____absorb_avx2;
    f_tyout := tyout_A64____absorb_avx2;
    f_res := res_A64____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
