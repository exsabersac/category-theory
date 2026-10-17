Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/monoidal+functor
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   本文件给出严格情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrictMonoidalFunctor.

Context {C D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.

Class StrictMonoidalFunctor : Type := {
  strict_functor_is_monoidal : @MonoidalFunctor C D _ _ F;

  (** Object-level strictness. *)
  strict_pure_obj : (@I D _) = F (@I C _);
  strict_ap_obj {x y : C} : (F x ⨂ F y)%object = F (x ⨂ y)%object;

  (** The comparison isomorphisms ARE the identity, transported. *)
  strict_pure_iso_id :
    to (@pure_iso _ _ _ _ F strict_functor_is_monoidal)
      ≈ match strict_pure_obj in _ = T return (@I D _) ~> T
        with eq_refl => id end;

  strict_ap_iso_id {x y : C} :
    to (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)
      ≈ match @strict_ap_obj x y in _ = T return (F x ⨂ F y)%object ~> T
        with eq_refl => id end
}.
#[export] Existing Instance strict_functor_is_monoidal.

(* Strict ⇒ strong by field projection; strong ⇒ lax is the library's
   existing [MonoidalFunctor_Is_Lax]. *)
Coercion strict_functor_is_monoidal : StrictMonoidalFunctor >-> MonoidalFunctor.

End StrictMonoidalFunctor.

Arguments StrictMonoidalFunctor {C D _ _} F.

(*
   本节说明 Strict 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fmap_match_id {C D : Category} (F : C ⟶ D) {x y : C} (e : x = y) :
  fmap[F] (match e in _ = T return x ~> T with eq_refl => id end)
    ≈ match f_equal F e in _ = T return F x ~> T with eq_refl => id end.
Proof. destruct e; simpl; apply fmap_id. Qed.

Lemma match_id_trans {C : Category} {x y z : C} (e1 : x = y) (e2 : y = z) :
  (match e2 in _ = T return y ~> T with eq_refl => id end)
    ∘ (match e1 in _ = T return x ~> T with eq_refl => id end)
    ≈ match eq_trans e1 e2 in _ = T return x ~> T with eq_refl => id end.
Proof. destruct e2, e1; simpl; cat. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrictMonoidalFunctorFrom.

Context {C D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.
Context `{S : @StrictMonoidalFunctor C D _ _ F}.

Corollary strict_pure_iso_from :
  from (@pure_iso _ _ _ _ F strict_functor_is_monoidal)
    ≈ match strict_pure_obj in _ = T return T ~> (@I D _)
      with eq_refl => id end.
Proof.
  apply (transported_iso_from
           strict_pure_obj
           (@pure_iso _ _ _ _ F strict_functor_is_monoidal)).
  apply strict_pure_iso_id.
Qed.

Corollary strict_ap_iso_from {x y : C} :
  from (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)
    ≈ match @strict_ap_obj _ _ _ _ F S x y in _ = T
        return T ~> (F x ⨂ F y)%object
      with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (@strict_ap_obj _ _ _ _ F S x y)
           (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)).
  apply strict_ap_iso_id.
Qed.

End StrictMonoidalFunctorFrom.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Id_StrictMonoidalFunctor `{@Monoidal C} :
  StrictMonoidalFunctor (Id[C]) := {
  strict_functor_is_monoidal := Id_MonoidalFunctor;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun _ _ => eq_refl
}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

#[export] Program Instance Compose_StrictMonoidalFunctor
  {C D E : Category}
  `{@Monoidal C} `{@Monoidal D} `{@Monoidal E}
  {G : D ⟶ E} {F : C ⟶ D}
  `{SG : @StrictMonoidalFunctor D E _ _ G}
  `{SF : @StrictMonoidalFunctor C D _ _ F} :
  StrictMonoidalFunctor (G ◯ F) := {
  strict_functor_is_monoidal :=
    Compose_MonoidalFunctor
      (@strict_functor_is_monoidal _ _ _ _ G SG)
      (@strict_functor_is_monoidal _ _ _ _ F SF);
  strict_pure_obj :=
    eq_trans (@strict_pure_obj _ _ _ _ G SG)
             (f_equal G (@strict_pure_obj _ _ _ _ F SF));
  strict_ap_obj := fun x y =>
    eq_trans (@strict_ap_obj _ _ _ _ G SG (F x) (F y))
             (f_equal G (@strict_ap_obj _ _ _ _ F SF x y))
}.
Next Obligation.
  unfold fobj_iso; simpl.
  rewrite (@strict_pure_iso_id _ _ _ _ F SF).
  rewrite (@strict_pure_iso_id _ _ _ _ G SG).
  rewrite fmap_match_id.
  apply match_id_trans.
Qed.
Next Obligation.
  simpl.
  pose proof (@strict_ap_iso_id _ _ _ _ F SF x y) as HF; simpl in HF.
  pose proof (@strict_ap_iso_id _ _ _ _ G SG (F x) (F y)) as HG; simpl in HG.
  rewrite HF, HG.
  rewrite fmap_match_id.
  apply match_id_trans.
Qed.
