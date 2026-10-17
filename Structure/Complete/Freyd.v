Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * Freyd's collapse: small complete 范畴 preorder （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/complete+small+category

   本文件给出完备范畴结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* Twin of Instance/Fun/Discrete.v's [cantor_bool], re-proved here
   because a Structure/ file does not require Instance/Fun.  Relocating the
   original to Lib/ is surfaced, not done. *)
Theorem freyd_cantor_bool {A : Type} (f : A → A → bool) :
  ¬ (∀ g : A → bool, exists a : A, ∀ x : A, f a x = g x).
Proof.
  intro H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  specialize (Ha a).
  destruct (f a a); discriminate.
Qed.

(* * ** The smallness witness 证明 所消耗 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record ArrowIndex (C : Category) := {
  ai_index   : Type;
  ai_enc     : ∀ {x y : C}, (x ~> y) → ai_index;
  ai_dec     : ∀ {x y : C}, ai_index → (x ~> y) → (x ~> y);
  ai_dec_enc : ∀ {x y : C} (h d : x ~> y), ai_dec (ai_enc h) d ≈ h
}.

Arguments ai_index {C} _.
Arguments ai_enc {C} _ {x y} _.
Arguments ai_dec {C} _ {x y} _ _.
Arguments ai_dec_enc {C} _ {x y} _ _.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ArrowIndex_op {C : Category} (AI : ArrowIndex C) :
  ArrowIndex (C^op) :=
  @Build_ArrowIndex (C^op) (ai_index AI)
    (fun x y h => ai_enc AI h)
    (fun x y m d => ai_dec AI m d)
    (fun x y h d => ai_dec_enc AI h d).

(* * ** The canonical witness: decidable 对象 equality suffices （已译） *)

(* Decidable 对象 equality is Construction/Quotient.v's [ObjDecEq]
 (a definitional class: 实例 IS decider), consumed as is —
 earlier revision declared duplicate [DecObj]; audit found the
 twin.（已译） *)

(* 相关说明。 （已译） *)
Definition td {C : Category} (DO : ObjDecEq C) {x y : obj[C]}
  (m : TotalMor C) (d : x ~> y) : x ~> y :=
  match DO (projT1 m) x with
  | left ex =>
      match DO (projT1 (projT2 m)) y with
      | left ey =>
          eq_rect (projT1 m) (fun u => u ~> y)
            (eq_rect (projT1 (projT2 m)) (fun v => projT1 m ~> v)
               (projT2 (projT2 m)) y ey)
            x ex
      | right _ => d
      end
  | right _ => d
  end.

Lemma td_enc {C : Category} (DO : ObjDecEq C) {x y : obj[C]} (h d : x ~> y) :
  td DO (existT _ x (existT _ y h)) d ≈ h.
Proof.
  unfold td; simpl.
  destruct (DO x x) as [ex | ne]; [| destruct (ne eq_refl)].
  destruct (DO y y) as [ey | ne]; [| destruct (ne eq_refl)].
  rewrite (UIP_dec DO ex eq_refl).
  rewrite (UIP_dec DO ey eq_refl).
  reflexivity.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition canonical_ArrowIndex {C : Category} (DO : ObjDecEq C) :
  ArrowIndex C :=
  {| ai_index   := TotalMor C
   ; ai_enc     := fun x y h => existT _ x (existT _ y h)
   ; ai_dec     := fun x y m d => td DO m d
   ; ai_dec_enc := fun x y h d => td_enc DO h d |}.

(* 相关说明。 （已译） *)

(*
   本节说明 Freyd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section FreydCore.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C}.
Context (f g : a ~> b).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* 相关说明。 （已译） *)
Context (sep : (a ~> b) → bool).
Context (sep_resp : ∀ u v : a ~> b, u ≈ v → sep u = sep v).
Context (sep_f : sep f = true).
Context (sep_g : sep g = false).

(* The [2^K]-indexed family of arrows [a ~> P]: at index [k] choose [f] or
   [g] according to [phi k]. *)
Definition fr_mk (phi : K → bool) : a ~> P :=
  unique_obj (iprod_desc HP (fun k => if phi k then f else g)).

Lemma fr_mk_commutes (phi : K → bool) (k : K) :
  pr k ∘ fr_mk phi ≈ (if phi k then f else g).
Proof.
  exact (unique_property (iprod_desc HP (fun k => if phi k then f else g)) k).
Qed.

(* Reading the choice back off an arrow, one index at a time. *)
Definition fr_decode (h : a ~> P) : K → bool := fun k => sep (pr k ∘ h).

Lemma fr_decode_mk (phi : K → bool) (k : K) : fr_decode (fr_mk phi) k = phi k.
Proof using sep_resp sep_f sep_g.
  unfold fr_decode.
  rewrite (sep_resp _ _ (fr_mk_commutes phi k)).
  destruct (phi k); assumption.
Qed.

(* Smallness turns [K] into a surjection onto the hom-set [a ~> P] ... *)
Definition fr_rd (k : K) : a ~> P := ai_dec AI k (fr_mk (fun _ => true)).

Lemma fr_rd_enc (h : a ~> P) : fr_rd (ai_enc AI h) ≈ h.
Proof. exact (ai_dec_enc AI h (fr_mk (fun _ => true))). Qed.

(* ... and hence into a K-indexed family of elements of [K → bool]. *)
Definition fr_Fam : K → K → bool := fun k => fr_decode (fr_rd k).

Lemma fr_Fam_surjective :
  ∀ phi : K → bool, exists k : K, ∀ i, fr_Fam k i = phi i.
Proof using sep_resp sep_f sep_g.
  intro phi.
  exists (ai_enc AI (fr_mk phi)).
  intro i.
  unfold fr_Fam, fr_decode.
  rewrite (sep_resp _ _ (compose_respects _ _ (reflexivity (pr i))
                           _ _ (fr_rd_enc (fr_mk phi)))).
  exact (fr_decode_mk phi i).
Qed.

(*
   本节说明 Freyd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem freyd_no_separated_pair : False.
Proof using All.
  exact (freyd_cantor_bool fr_Fam fr_Fam_surjective).
Qed.

End FreydCore.

(* 相关说明。 （已译） *)

(* [≈] is Type-valued (Lib/Setoid.v), so the decider is a [sum]. *)
Definition DecHom (C : Category) : Type :=
  ∀ (x y : C) (u v : x ~> y), ((u ≈ v) + ((u ≈ v) → False))%type.

Definition DecHom_op {C : Category} (D : DecHom C) : DecHom (C^op) :=
  fun x y u v => D y x u v.

(* 相关说明。 （已译） *)
Section Separator.

Context {C : Category} (D : DecHom C) {x y : C} (f g : x ~> y)
  (Hne : (f ≈ g) → False).

Definition fr_sep (h : x ~> y) : bool := if D x y h f then true else false.

Lemma fr_sep_resp (u v : x ~> y) : u ≈ v → fr_sep u = fr_sep v.
Proof.
  intro Huv; unfold fr_sep.
  destruct (D x y u f) as [Hu | Hu]; destruct (D x y v f) as [Hv | Hv];
    try reflexivity.
  - destruct (Hv (transitivity (symmetry Huv) Hu)).
  - destruct (Hu (transitivity Huv Hv)).
Qed.

Lemma fr_sep_f : fr_sep f = true.
Proof.
  unfold fr_sep.
  destruct (D x y f f) as [Hff | Hff]; [reflexivity |].
  destruct (Hff (reflexivity f)).
Qed.

Lemma fr_sep_g : fr_sep g = false.
Proof using Hne.
  unfold fr_sep.
  destruct (D x y g f) as [Hgf | Hgf]; [| reflexivity].
  destruct (Hne (symmetry Hgf)).
Qed.

End Separator.

(* Mac Lane §V.2 Proposition 3 / Riehl §3.7 Proposition 3.7.3, over the
   class of indexed products: arrows indexed by [K], products over [K],
   decidable hom-setoids ⇒ thin. *)
Theorem freyd_thin {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (indexed_product (fun _ : ai_index AI => y))
           (indexed_product_proj (fun _ : ai_index AI => y))
           (indexed_product_ump (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Assembled at C's own arrow collection. *)
Definition freyd_thin_canonical {C : Category}
  (DO : ObjDecEq C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C :=
  freyd_thin (canonical_ArrowIndex DO) HP D.

(* Riehl §E.1's "or coproducts": products in [C^op], thinness self-dual. *)
Definition freyd_thin_dual {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts (C^op)) (D : DecHom C) : Thin C :=
  Opposite_Thin (freyd_thin (ArrowIndex_op AI) HP (DecHom_op D)).

(* 相关说明。 （已译） *)

Section Wall.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C} (f g : a ~> b) (Hne : (f ≈ g) → False).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* 相关说明。 （已译） *)
Lemma fr_mk_injective (phi psi : K → bool) :
  fr_mk AI f g P pr HP phi ≈ fr_mk AI f g P pr HP psi → ∀ k, phi k = psi k.
Proof using Hne.
  intros Heq k.
  pose proof (fr_mk_commutes AI f g P pr HP phi k) as Hp.
  pose proof (fr_mk_commutes AI f g P pr HP psi k) as Hq.
  assert (Hc : (if phi k then f else g) ≈ (if psi k then f else g)).
  { rewrite <- Hp, <- Hq.
    apply compose_respects; [reflexivity | exact Heq]. }
  destruct (phi k); destruct (psi k); try reflexivity.
  - destruct (Hne Hc).
  - destruct (Hne (symmetry Hc)).
Qed.

(* 相关说明。 （已译） *)
Definition fr_inj (phi : K → bool) : K := ai_enc AI (fr_mk AI f g P pr HP phi).

Lemma fr_inj_injective (phi psi : K → bool) :
  fr_inj phi = fr_inj psi → ∀ k, phi k = psi k.
Proof using Hne.
  intro He.
  apply fr_mk_injective.
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP phi) (fr_mk AI f g P pr HP phi)).
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP psi) (fr_mk AI f g P pr HP phi)).
  unfold fr_inj in He; rewrite He; reflexivity.
Qed.

End Wall.

(* 相关说明。 （已译） *)

Section CompleteBridge.

Universe o h p uo uh up.

Context {C : Category@{uo uh up}} (comp : @Complete C).

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition complete_iprod_obj {A : Type@{o}} (d : A → C) : C :=
  vertex_obj[@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))].

Definition complete_iprod_proj {A : Type@{o}} (d : A → C) (i : A) :
  complete_iprod_obj d ~> d i :=
  cone_leg (@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))) i.

Definition complete_iprod {A : Type@{o}} (d : A → C) :
  IsIndexedProduct d (complete_iprod_obj d) (complete_iprod_proj d) :=
  discrete_IsIndexedProduct_of_IsLimitCone
    (DiscreteCat_Functor' d)
    (@limit_cone _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d)))
    (@ump_limits _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))).

End CompleteBridge.

(* The issue's pinned statement: 范畴 whose arrows indexed a
 type at it complete, decidable hom-setoids, thin. （已译） *)
Theorem small_complete_is_thin {C : Category}
  (AI : ArrowIndex C) (comp : @Complete C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (complete_iprod_obj comp (fun _ : ai_index AI => y))
           (complete_iprod_proj comp (fun _ : ai_index AI => y))
           (complete_iprod comp (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Riehl §E.1's cocomplete half. *)
Definition small_cocomplete_is_thin {C : Category}
  (AI : ArrowIndex C) (cocomp : @Cocomplete C) (D : DecHom C) : Thin C :=
  Opposite_Thin
    (small_complete_is_thin (ArrowIndex_op AI)
       (Complete_op_of_Cocomplete cocomp) (DecHom_op D)).

(* 相关说明。 （已译） *)

(*
   本节说明 Freyd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition complete_has_glbs {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : HasAllMeets (thin_preorder C).
Proof.
  intros Ix d.
  exists (complete_iprod_obj comp d).
  split.
  - intro i; exact (inhabits (complete_iprod_proj comp d i)).
  - intros n Hn.
    exact (inhabits (unique_obj (iprod_desc (complete_iprod comp d)
             (fun i => ch n (d i) (Hn i))))).
Defined.

(* Through #422's characterisation (Instance/Proset/Limit.v), the preorder
   reflection of a complete category is itself a complete preorder. *)
Definition complete_Proset_Complete {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : @Complete (Proset (thin_PreOrder C)) :=
  snd (proset_Complete_iff_all_meets (thin_PreOrder C))
      (complete_has_glbs comp ch).
