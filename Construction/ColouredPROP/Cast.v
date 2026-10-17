Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CT_cast {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) : CTerm S cs ds :=
  match e in _ = k return CTerm S cs k with
  | eq_refl => CT_id cs
  end.

(** Cast at [eq_refl] is the literal identity. *)
Lemma CT_cast_refl {Colour : Type} {S : CSignature Colour}
  (cs : list Colour) :
  @CT_cast Colour S cs cs eq_refl = CT_id cs.
Proof. reflexivity. Qed.

(** Composing two casts gives a cast along the transitive equation. *)
Lemma CT_cast_compose {Colour : Type} {S : CSignature Colour}
  {cs ds es : list Colour} (e1 : cs = ds) (e2 : ds = es) :
  CTermEq S (CT_comp (CT_cast e2) (CT_cast e1)) (CT_cast (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  cbn.
  apply CTE_id_left.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Casting along [e] after casting along [eq_sym e] 恒等
 TARGET word [ds]. （已译） *)
Lemma CT_cast_inv {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast e) (CT_cast (eq_sym e))) (CT_id ds).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(** Casting along [eq_sym e] after casting along [e] 恒等
 SOURCE word [cs]. （已译） *)
Lemma CT_cast_inv_sym {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast (eq_sym e)) (CT_cast e)) (CT_id cs).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_cast_natural {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds)
  (f : CTerm S cs cs) (g : CTerm S ds ds)
  (Hfg : forall (q : cs = ds),
           CTermEq S (CT_comp (CT_cast q) f)
                     (CT_comp g (CT_cast q))) :
  CTermEq S (CT_comp (CT_cast e) f) (CT_comp g (CT_cast e)).
Proof. apply Hfg. Qed.

(** Degenerate naturality at [eq_refl]: a [CT_cast eq_refl] is
    [CT_id], so it commutes with any morphism trivially. *)
Lemma CT_cast_natural_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (f : CTerm S cs cs) :
  CTermEq S (CT_comp (CT_cast eq_refl) f) (CT_comp f (CT_cast eq_refl)).
Proof.
  cbn.
  apply CTE_trans with f.
  - apply CTE_id_left.
  - apply CTE_sym, CTE_id_right.
Qed.

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_term_eq_rect_destruct {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) (t : CTerm S cs cs) :
  eq_rect cs (fun k => CTerm S cs k) t ds e
  = match e in _ = k return CTerm S cs k with
    | eq_refl => t
    end.
Proof. destruct e; reflexivity. Qed.

(** 本节：Dual: [eq_rect_r] transport domain index reduces at
 [eq_refl] term itself. More general transport shapes
 require [destruct e] context. （已译） *)
Lemma CT_term_eq_rect_r_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (t : CTerm S cs cs) :
  eq_rect_r (fun k => CTerm S k cs) t (@eq_refl _ cs) = t.
Proof. reflexivity. Qed.

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_tens_id_cast_left {Colour : Type} {S : CSignature Colour}
  {cs a b : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_id cs) (CT_cast e))
            (CT_cast (f_equal (fun ks => cs ++ ks) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(** Symmetric variant: cast LEFT, 恒等 RIGHT. （已译） *)
Lemma CT_tens_cast_id_right {Colour : Type} {S : CSignature Colour}
  {a b ns : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_cast e) (CT_id ns))
            (CT_cast (f_equal (fun ks => ks ++ ns) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_tens_id_id {Colour : Type} {S : CSignature Colour}
  (cs ds : list Colour) :
  CTermEq S (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds)).
Proof. apply CTE_tens_id. Qed.

(* * Composing trivial [CT_cast eq_refl] (which is [CT_id]) onto a
 tensor is 恒等 operation. [CT_cast eq_refl] reduces to
 [CT_id (ds1 ++ ds2)], so composite collapses left
 恒等.（已译） *)
Lemma CT_comp_cast_tens_left {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_cast eq_refl) (CT_tens f g))
            (CT_tens f g).
Proof. cbn. apply CTE_id_left. Qed.

(** Dual: post-composing a trivial [CT_cast eq_refl] on the input
    side of a tensor collapses by right identity. *)
Lemma CT_comp_tens_cast_right {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_tens f g) (CT_cast eq_refl))
            (CT_tens f g).
Proof. cbn. apply CTE_id_right. Qed.

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CT_cast_irrelevant {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs ds : list Colour} (e1 e2 : cs = ds) :
  CT_cast (S := S) e1 = CT_cast (S := S) e2.
Proof.
  rewrite (UIP_dec (list_eq_dec Cdec) e1 e2).
  reflexivity.
Qed.

(** Special case: any cast along equation [cs = cs] the
 恒等, because [eq_refl cs] canonical 证明 of
 [cs = cs] [CT_cast eq_refl = CT_id cs] reduces
 definitionally. （已译） *)
Lemma CT_cast_id {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs : list Colour} (e : cs = cs) :
  CT_cast (S := S) e = CT_id cs.
Proof.
  rewrite (CT_cast_irrelevant Cdec e eq_refl).
  reflexivity.
Qed.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/associator
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Coherence_condition

   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CFreeCat_unit_left {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) ([] ++ cs) cs :=
  @Build_Isomorphism (CFreeCat S) ([] ++ cs) cs
    (CT_cast (app_nil_l cs))
    (CT_cast (eq_sym (app_nil_l cs)))
    (CT_cast_inv (app_nil_l cs))
    (CT_cast_inv_sym (app_nil_l cs)).

(** Right unitor [cs ++ [] ≅ cs] in [CFreeCat S].  [app_nil_r] is
    propositional, not definitional, so the cast is along a
    non-trivial equation. *)
Definition CFreeCat_unit_right {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) (cs ++ []) cs :=
  @Build_Isomorphism (CFreeCat S) (cs ++ []) cs
    (CT_cast (app_nil_r cs))
    (CT_cast (eq_sym (app_nil_r cs)))
    (CT_cast_inv (app_nil_r cs))
    (CT_cast_inv_sym (app_nil_r cs)).

(*
   本节说明 Cast 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CFreeCat_tensor_assoc {Colour : Type} (S : CSignature Colour)
  (x y z : list Colour) :
  @Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z)) :=
  @Build_Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z))
    (CT_cast (eq_sym (app_assoc x y z)))
    (CT_cast (app_assoc x y z))
    (CT_cast_inv_sym (app_assoc x y z))
    (CT_cast_inv (app_assoc x y z)).

Arguments CFreeCat_unit_left {Colour} S cs : assert.
Arguments CFreeCat_unit_right {Colour} S cs : assert.
Arguments CFreeCat_tensor_assoc {Colour} S x y z : assert.
