Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Program Definition FunnySwap_sep {C D : Category} :
  SepFunctorial (E := D □ C) (fun (c : C) (d : D) => (d, c)) := {|
  sf_lmap := fun c c' f d => rstep f;
  sf_rmap := fun c d d' g => lstep g
|}.
Next Obligation.
  proper.
  apply feq_consR; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation. exact (feq_idR fnil). Qed.
Next Obligation. exact (feq_idL fnil). Qed.
Next Obligation. apply feq_sym; apply feq_fuseR. Qed.
Next Obligation. apply feq_sym; apply feq_fuseL. Qed.

Definition FunnySwap {C D : Category} : (C □ D) ⟶ (D □ C) :=
  FunnyUP FunnySwap_sep.

(*
   本节说明 Swap 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma FunnySwap_fnil {C D : Category} {c : C} {d : D} :
  @fmap (C □ D) (D □ C) FunnySwap (c, d) (c, d) fnil = fnil.
Proof. reflexivity. Qed.

Lemma FunnySwap_fconsL {C D : Category} {c1 c2 : C} {d1 : D} {c3 : C} {d3 : D}
  (f : c1 ~{C}~> c2) (t : FunHom c2 d1 c3 d3) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d1) (c3, d3) (fconsL f t)
    = fconsR f (@fmap (C □ D) (D □ C) FunnySwap (c2, d1) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnySwap_fconsR {C D : Category} {c1 : C} {d1 d2 : D} {c3 : C} {d3 : D}
  (g : d1 ~{D}~> d2) (t : FunHom c1 d2 c3 d3) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d1) (c3, d3) (fconsR g t)
    = fconsL g (@fmap (C □ D) (D □ C) FunnySwap (c1, d2) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnySwap_lstep {C D : Category} {c1 c2 : C} {d : D}
  (f : c1 ~{C}~> c2) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d) (c2, d) (lstep f) = rstep f.
Proof. reflexivity. Qed.

Lemma FunnySwap_rstep {C D : Category} {c : C} {d1 d2 : D}
  (g : d1 ~{D}~> d2) :
  @fmap (C □ D) (D □ C) FunnySwap (c, d1) (c, d2) (rstep g) = lstep g.
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma FunnySwap_invol {C D : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C □ D))
    (@FunnySwap D C ◯ @FunnySwap C D) Id.
Proof.
  apply (Funny_strict_eq (@FunnySwap D C ◯ @FunnySwap C D) Id
           (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

(* * ** Strict 自然性 both variables

 Both composites send [lstep f] [rstep (fmap[F] f)] [rstep g] to
 [lstep (fmap[G] g)] definitionally, agree definitionally on
 explicit-pair 对象. （已译） *)

Lemma FunnySwap_natural {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (D' □ C'))
    (@FunnySwap C' D' ◯ FunnyBimap F G) (FunnyBimap G F ◯ @FunnySwap C D).
Proof.
  apply (Funny_strict_eq (@FunnySwap C' D' ◯ FunnyBimap F G)
           (FunnyBimap G F ◯ @FunnySwap C D) (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Funny_swap {C D : Category} : (C □ D) ≅[StrictCat] (D □ C) :=
  @Build_Isomorphism StrictCat (C □ D) (D □ C)
    (@FunnySwap C D) (@FunnySwap D C)
    (@FunnySwap_invol D C) (@FunnySwap_invol C D).

Definition Funny_swap_cat {C D : Category} : (C □ D) ≅[Cat] (D □ C) :=
  fobj_iso StrictCat_to_Cat (C □ D) (D □ C) Funny_swap.
