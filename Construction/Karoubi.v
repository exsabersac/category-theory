Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

(** The Karoubi envelope (idempotent splitting completion) of a category. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/Karoubi+envelope
   nLab:  https://ncatlab.org/nlab/show/Cauchy+complete+category
   Paper: Karoubi, "K-Theory: An Introduction", Springer 1978
   Paper: Hayashi, "Adjunction of semifunctors: categorical structures
   Paper: Lawvere, "Metric spaces, generalized logic, and closed
   Paper: Borceux, Dejean, "Cauchy completion in category theory",

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Program Definition Karoubi (C : Category) : Category := {|
  obj := ∃ (x : C) (e : x ~> x), e ∘ e ≈ e;
  hom := fun X Y =>
    ∃ f : `1 X ~> `1 Y, (`1 (`2 Y) ∘ f ≈ f) ∧ (f ∘ `1 (`2 X) ≈ f);
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id := fun X => (`1 (`2 X); _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation.
  (* the hom-setoid: equivalence of the underlying C-morphisms *)
  intros C X Y.
  equivalence.
Qed.
Next Obligation.
  (* the identity on (x, e) is e; both absorption laws read e ∘ e ≈ e *)
  intros C X.
  destruct X as [x [e He]]; simpl.
  split.
  - exact He.
  - exact He.
Qed.
Next Obligation.
  (* composition: each absorption law comes from the nearer factor *)
  intros C X Y Z f g.
  destruct f as [f [fl fr]], g as [g [gl gr]]; simpl in *.
  split.
  - rewrite comp_assoc, fl.
    reflexivity.
  - rewrite <- comp_assoc, gr.
    reflexivity.
Qed.
Next Obligation.
  (* compose respects ≈, inherited from C *)
  intros C X Y Z f g Hfg h k Hhk; simpl in *.
  now rewrite Hfg, Hhk.
Qed.
Next Obligation.
  (* id_left: e_y ∘ f ≈ f is f's left absorption law *)
  intros C X Y f.
  destruct f as [f [fl fr]]; simpl.
  exact fl.
Qed.
Next Obligation.
  (* id_right: f ∘ e_x ≈ f is f's right absorption law *)
  intros C X Y f.
  destruct f as [f [fl fr]]; simpl.
  exact fr.
Qed.
Next Obligation.
  intros C X Y Z W f g h; simpl.
  apply comp_assoc.
Qed.
Next Obligation.
  intros C X Y Z W f g h; simpl.
  apply comp_assoc_sym.
Qed.

(* The canonical full and faithful embedding C ⟶ Split(C), sending x to the
   trivially split idempotent (x, id[x]) and acting as the identity on
   morphisms. *)
Program Definition Karoubi_Embed {C : Category} : C ⟶ Karoubi C := {|
  fobj := fun x => (x; (id[x]; _));
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation.
  intros C x; simpl.
  apply id_left.
Qed.
Next Obligation.
  intros C x y f; simpl.
  split.
  - apply id_left.
  - apply id_right.
Qed.
Next Obligation.
  intros C x y f g Hfg; simpl.
  exact Hfg.
Qed.
Next Obligation.
  intros C x; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; simpl.
  reflexivity.
Qed.

(* The embedding is full: a morphism (x, id) ~> (y, id) of Split(C) is
   carried by a C-morphism x ~> y, which is its own preimage. *)
#[export] Program Instance Karoubi_Embed_Full {C : Category} :
  Full (@Karoubi_Embed C) := {
  prefmap := fun _ _ g => `1 g
}.
Next Obligation.
  intros C x y g; simpl.
  reflexivity.
Qed.

(* The embedding is faithful: equality of images is literally equality of the
   underlying morphisms. *)
#[export] Program Instance Karoubi_Embed_Faithful {C : Category} :
  Faithful (@Karoubi_Embed C).
Next Obligation.
  intros C x y f g Hfg.
  exact Hfg.
Qed.

(*
   本节说明 Karoubi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition karoubi_idem_splits {C : Category} (X : Karoubi C)
        (φ : X ~{Karoubi C}~> X) (H : Idempotent φ) :
  @SplitIdempotent (Karoubi C) X (`1 X; (`1 φ; @idem _ _ _ H)) := {|
  split_idem   := φ;
  split_idem_r := (`1 φ; _);
  split_idem_s := (`1 φ; _)
|}.
Next Obligation.
  (* the retraction X ~> (x, φ): absorption by φ above, by e below *)
  intros C X φ H; simpl.
  split.
  - exact (@idem _ _ _ H).
  - exact (snd (`2 φ)).
Qed.
Next Obligation.
  (* the section (x, φ) ~> X: absorption by e above, by φ below *)
  intros C X φ H; simpl.
  split.
  - exact (fst (`2 φ)).
  - exact (@idem _ _ _ H).
Qed.
Next Obligation.
  (* s ∘ r ≈ φ, i.e. φ ∘ φ ≈ φ *)
  intros C X φ H; simpl.
  exact (@idem _ _ _ H).
Qed.
Next Obligation.
  (* r ∘ s ≈ id on (x, φ), whose identity is carried by φ *)
  intros C X φ H; simpl.
  exact (@idem _ _ _ H).
Qed.
