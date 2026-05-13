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

(* A1184____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_16186 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16186).
Definition offset_16187 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16187).
Definition DELTA_16188 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16188).
Definition LEN_16189 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16189).
Definition TRAIL_16190 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16190).
Definition CUR_16191 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16191).
Definition AT_16192 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16192).
Definition w256_16193 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16193).
Definition AT8_16194 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16194).
Definition w_16195 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16195).
Definition t128_16196 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16196).

(* Signature *)
Definition tyin_A1184____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_16186.(gv)
    ; offset_16187.(gv)
    ; DELTA_16188.(gv)
    ; LEN_16189.(gv)
    ; TRAIL_16190.(gv)
    ; CUR_16191.(gv)
    ; AT_16192.(gv) ].
Definition tyout_A1184____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1184____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_16188.(gv)
    ; LEN_16189.(gv)
    ; TRAIL_16190.(gv)
    ; AT_16192.(gv)
    ; w256_16193.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16192) (Pvar CUR_16191)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16191) (Pconst (8)%Z)) (Pvar AT_16192))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16189) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16190) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_16193.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16189))
              [:: cassgn (Lvar AT8_16194.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16192) (Pvar CUR_16191))
                ; copn [:: Lvar w256_16193.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_16186 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16187) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16188)))) ]
                ; ccall [:: Lvar w256_16193.(gv) ] __SHLQ_256 [:: Pvar w256_16193
                                                                ; Pvar AT8_16194 ]
                ; cassgn (Lvar DELTA_16188.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16188) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16194)))
                ; cassgn (Lvar LEN_16189.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16189) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16194)))
                ; cassgn (Lvar AT_16192.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16191) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_16194.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16192) (Pvar CUR_16191))
                ; ccall [:: Lvar DELTA_16188.(gv)
                          ; Lvar LEN_16189.(gv)
                          ; Lvar TRAIL_16190.(gv)
                          ; Lvar AT_16192.(gv)
                          ; Lvar w_16195.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16186
                                                                    ; Pvar offset_16187
                                                                    ; Pvar DELTA_16188
                                                                    ; Pvar LEN_16189
                                                                    ; Pvar TRAIL_16190
                                                                    ; Pvar CUR_16191
                                                                    ; Pvar AT_16192 ]
                ; cassgn (Lvar t128_16196.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_16195))
                ; copn [:: Lvar w256_16193.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_16196 ]
                ; ccall [:: Lvar w256_16193.(gv) ] __SHLQ_256 [:: Pvar w256_16193
                                                                ; Pvar AT8_16194 ] ] ] ].

Definition fd_A1184____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_bcast_upto8_at;
    f_params := args_A1184____a_ilen_read_bcast_upto8_at;
    f_body := body_A1184____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1184____a_ilen_read_bcast_upto8_at;
    f_res := res_A1184____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
