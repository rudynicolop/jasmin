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

(* A128____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_64 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16394).
Definition AT_61 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16395).
Definition buf_94 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16396).
Definition offset_89 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16397).
Definition _LEN_57 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16398).
Definition _TRAILB_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16399).
Definition DELTA_61 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16400).
Definition AT8_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16401).
Definition w_66 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16402).
Definition j_at_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16403).

(* Signature *)
Definition tyin_A128____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 128; aword U64; aint; aint ].
Definition args_A128____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_64.(gv)
    ; AT_61.(gv)
    ; buf_94.(gv)
    ; offset_89.(gv)
    ; _LEN_57.(gv)
    ; _TRAILB_33.(gv) ].
Definition tyout_A128____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A128____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_64.(gv); AT_61.(gv); offset_89.(gv) ].

(* Body *)
Definition body_A128____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_61.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_23.(gv)) AT_none (aint) (Pvar AT_61))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_61.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_61) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_23) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_61.(gv)
                                                                ; Lvar _LEN_57.(gv)
                                                                ; Lvar _TRAILB_33.(gv)
                                                                ; Lvar AT8_23.(gv)
                                                                ; Lvar w_66.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_94
                                                                    ; Pvar offset_89
                                                                    ; Pvar DELTA_61
                                                                    ; Pvar _LEN_57
                                                                    ; Pvar _TRAILB_33
                                                                    ; Pvar AT_61
                                                                    ; Pvar AT8_23 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_66.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_66) (Pget Aligned AAscale U256 st_64 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_61) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_64.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_61) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_66))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_61.(gv)) AT_none (aint) (Pvar AT8_23)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_89.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_89) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_61))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_9.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_61) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_61) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_57) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_66.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_94 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_89)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_89.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_89) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_66.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_66) (Pget Unaligned AAdirect U256 st_64 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_9)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_64.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_9))) AT_none (aword U256) (Pvar w_66))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_61.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_61) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_57) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_57.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_57) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_57)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_33) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_61.(gv)
                                                                ; Lvar _LEN_57.(gv)
                                                                ; Lvar _TRAILB_33.(gv)
                                                                ; Lvar AT_61.(gv)
                                                                ; Lvar w_66.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_94
                                                                    ; Pvar offset_89
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_57
                                                                    ; Pvar _TRAILB_33
                                                                    ; Pvar AT_61
                                                                    ; Pvar AT_61 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_66.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_66) (Pget Unaligned AAdirect U256 st_64 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_9)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_64.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_9))) AT_none (aword U256) (Pvar w_66))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_89.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_89) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_61)))) ]
                              [::]) ].

Definition fd_A128____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____addstate_bcast_avx2x4;
    f_params := args_A128____addstate_bcast_avx2x4;
    f_body := body_A128____addstate_bcast_avx2x4;
    f_tyout := tyout_A128____addstate_bcast_avx2x4;
    f_res := res_A128____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
