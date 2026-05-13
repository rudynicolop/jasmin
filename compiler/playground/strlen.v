From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Axiom IdO : IdentOracles.
Existing Instance IdO.

(* -------------------------------------------------------------------------- *)
(* Globals *)

Definition strlen_gds : glob_decls := [::].

(* -------------------------------------------------------------------------- *)
(* Function names *)

Definition strlen : funname := mkfname 155.
Definition main : funname := mkfname 165.

(* -------------------------------------------------------------------------- *)
(* Functions *)

(* strlen *)
(* Local variables *)
Definition str : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 177).
Definition len : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 178).
Definition c : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 179).

(* Signature *)
Definition tyin_strlen : seq atype := [:: aword U64 ].
Definition args_strlen : seq var_i := [:: str.(gv) ].
Definition tyout_strlen : seq atype := [:: aword U8 ].
Definition res_strlen : seq var_i := [:: len.(gv) ].

(* Body *)
Definition body_strlen : cmd :=
  [:: cassgn (Lvar len.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))
    ; cwhile
        [:: cassgn (Lvar c.(gv)) (aword U8) (Pload Unaligned U8 (Pvar str)) ]
        (Papp2 (Oneq (Op_w U8)) (Pvar c) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)))
        [:: cassgn (Lvar str.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar str) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)))
          ; cassgn (Lvar len.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar len) (Papp1 (Oword_of_int U8) (Pconst (1)%Z))) ] ].

Definition fd_strlen : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_strlen;
    f_params := args_strlen;
    f_body := body_strlen;
    f_tyout := tyout_strlen;
    f_res := res_strlen;
    f_extra := tt;
  |}.

(* main *)
(* Local variables *)
Definition argc : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 173).
Definition argv : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 174).
Definition len_175 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 175).
Definition input : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 176).

(* Signature *)
Definition tyin_main : seq atype := [:: aword U64; aword U64 ].
Definition args_main : seq var_i := [:: argc.(gv); argv.(gv) ].
Definition tyout_main : seq atype := [:: aword U8 ].
Definition res_main : seq var_i := [:: len_175.(gv) ].

(* Body *)
Definition body_main : cmd :=
  [:: cassgn (Lvar len_175.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Papp1 (Oneg (Op_int)) (Pconst (1)%Z)))
    ; cif
        (Papp2 (Oeq (Op_w U64)) (Pvar argc) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)))
        [:: cassgn (Lvar input.(gv)) (aword U64) (Pload Unaligned U64 (Papp2 (Oadd (Op_w U64)) (Pvar argv) (Papp1 (Oword_of_int U64) (Pconst (8)%Z))))
          ; ccall [:: Lvar len_175.(gv) ] strlen [:: Pvar input ] ]
        [::] ].

Definition fd_main : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_main;
    f_params := args_main;
    f_body := body_main;
    f_tyout := tyout_main;
    f_res := res_main;
    f_extra := tt;
  |}.

(* -------------------------------------------------------------------------- *)
(* Program *)

Definition strlen : uprog :=
  {|
    p_globs := strlen_gds;
    p_funcs := [:: (strlen, fd_strlen); (main, fd_main) ];
    p_extra := tt;
  |}.
