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

(* __addstate_m_bcast_avx2x4 *)
(* Local variables *)
Definition st_10 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18544).
Definition AT_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18545).
Definition buf_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18546).
Definition _LEN_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18547).
Definition _TRAILB_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18548).
Definition AT8_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18549).
Definition w_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18550).
Definition j_at : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18551).

(* Signature *)
Definition tyin___addstate_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64; aint; aint ].
Definition args___addstate_m_bcast_avx2x4 : seq var_i :=
  [:: st_10.(gv); AT_5.(gv); buf_12.(gv); _LEN_3.(gv); _TRAILB_1.(gv) ].
Definition tyout___addstate_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res___addstate_m_bcast_avx2x4 : seq var_i :=
  [:: st_10.(gv); AT_5.(gv) ].

(* Body *)
Definition body___addstate_m_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar AT8_1.(gv)) AT_none (aint) (Pvar AT_5))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_5.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_5) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_1) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_12.(gv)
                                                                ; Lvar _LEN_3.(gv)
                                                                ; Lvar _TRAILB_1.(gv)
                                                                ; Lvar AT8_1.(gv)
                                                                ; Lvar w_7.(gv) ] __m_ilen_read_bcast_upto8_at [:: Pvar buf_12
                                                                    ; Pvar _LEN_3
                                                                    ; Pvar _TRAILB_1
                                                                    ; Pvar AT_5
                                                                    ; Pvar AT8_1 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_7.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_7) (Pget Aligned AAscale U256 st_10 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_5) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_10.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_5) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_5.(gv)) AT_none (aint) (Pvar AT8_1)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar j_at.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_5) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_5) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_3) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_12)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar buf_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_7.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_7) (Pget Unaligned AAdirect U256 st_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_10.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))) AT_none (aword U256) (Pvar w_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_5.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_5) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_3) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_3.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_3) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_3)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_1) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_12.(gv)
                                                                ; Lvar _LEN_3.(gv)
                                                                ; Lvar _TRAILB_1.(gv)
                                                                ; Lvar AT_5.(gv)
                                                                ; Lvar w_7.(gv) ] __m_ilen_read_bcast_upto8_at [:: Pvar buf_12
                                                                    ; Pvar _LEN_3
                                                                    ; Pvar _TRAILB_1
                                                                    ; Pvar AT_5
                                                                    ; Pvar AT_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_7.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_7) (Pget Unaligned AAdirect U256 st_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_10.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))) AT_none (aword U256) (Pvar w_7)) ]
                              [::]) ].

Definition fd___addstate_m_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addstate_m_bcast_avx2x4;
    f_params := args___addstate_m_bcast_avx2x4;
    f_body := body___addstate_m_bcast_avx2x4;
    f_tyout := tyout___addstate_m_bcast_avx2x4;
    f_res := res___addstate_m_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
