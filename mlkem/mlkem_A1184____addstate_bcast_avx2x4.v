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

(* A1184____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_74 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16012).
Definition AT_71 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16013).
Definition buf_108 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16014).
Definition offset_106 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16015).
Definition _LEN_67 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16016).
Definition _TRAILB_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16017).
Definition DELTA_72 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16018).
Definition AT8_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16019).
Definition w_76 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16020).
Definition j_at_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16021).

(* Signature *)
Definition tyin_A1184____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1184; aword U64; aint; aint ].
Definition args_A1184____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_74.(gv)
    ; AT_71.(gv)
    ; buf_108.(gv)
    ; offset_106.(gv)
    ; _LEN_67.(gv)
    ; _TRAILB_39.(gv) ].
Definition tyout_A1184____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1184____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_74.(gv); AT_71.(gv); offset_106.(gv) ].

(* Body *)
Definition body_A1184____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_72.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_27.(gv)) AT_none (aint) (Pvar AT_71))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_71.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_71) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_27) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_72.(gv)
                                                                ; Lvar _LEN_67.(gv)
                                                                ; Lvar _TRAILB_39.(gv)
                                                                ; Lvar AT8_27.(gv)
                                                                ; Lvar w_76.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_108
                                                                    ; Pvar offset_106
                                                                    ; Pvar DELTA_72
                                                                    ; Pvar _LEN_67
                                                                    ; Pvar _TRAILB_39
                                                                    ; Pvar AT_71
                                                                    ; Pvar AT8_27 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_76.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_76) (Pget Aligned AAscale U256 st_74 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_71) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_74.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_71) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_76))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_71.(gv)) AT_none (aint) (Pvar AT8_27)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_106.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_106) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_72))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_11.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_71) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_11) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_71) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_67) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_76.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_106)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_106.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_106) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_76.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_76) (Pget Unaligned AAdirect U256 st_74 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_11)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_74.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_11))) AT_none (aword U256) (Pvar w_76))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_11.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_11) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_71.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_71) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_67) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_67.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_67) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_67)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_39) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_72.(gv)
                                                                ; Lvar _LEN_67.(gv)
                                                                ; Lvar _TRAILB_39.(gv)
                                                                ; Lvar AT_71.(gv)
                                                                ; Lvar w_76.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_108
                                                                    ; Pvar offset_106
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_67
                                                                    ; Pvar _TRAILB_39
                                                                    ; Pvar AT_71
                                                                    ; Pvar AT_71 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_76.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_76) (Pget Unaligned AAdirect U256 st_74 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_11)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_74.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_11))) AT_none (aword U256) (Pvar w_76))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_106.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_106) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_72)))) ]
                              [::]) ].

Definition fd_A1184____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____addstate_bcast_avx2x4;
    f_params := args_A1184____addstate_bcast_avx2x4;
    f_body := body_A1184____addstate_bcast_avx2x4;
    f_tyout := tyout_A1184____addstate_bcast_avx2x4;
    f_res := res_A1184____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
