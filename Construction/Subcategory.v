Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Subcategory.

Context (C : Category).

(** A subcategory D of a category C. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Subcategory

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record Subcategory := {
  sobj : C → Type;                  (* sub-collection of the objects of C *)

  (* sub-collection of the C-morphisms between selected objects *)
  shom {x y : C} : sobj x → sobj y → (x ~> y) → Type;

  (* closed under 复合: if f : y ~> z g : x ~> y D, then so
 复合 f ∘ g : x ~> z （已译） *)
  scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
        {f : y ~> z} {g : x ~> y} :
    shom oy oz f → shom ox oy g → shom ox oz (f ∘ g);

  (* closed under identity: if x is in D then so is the identity 1ₓ *)
  sid {x : C} (ox : sobj x) : shom ox ox (@id C x)
}.

Variable S : Subcategory.

(* These conditions ensure that D is a category in its own right... *)
Program Definition Sub : Category := {|
  obj     := { x : C & sobj S x };
  hom     := fun x y => { f : `1 x ~> `1 y & shom S `2 x `2 y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; sid S `2 x);
  compose := fun x y z f g  => (`1 f ∘ `1 g; scomp S `2 x `2 y `2 z `2 f `2 g)
|}.

(* ... 含入 D ⟶ C 函子. （已译） *)
Program Instance Incl : Sub ⟶ C := {
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
}.

(*
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5, Remark 1.5.8,

   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Incl_Faithful : Functor.Faithful Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(* Additionally, we say D is...

 A full subcategory if any x y D, every 态射 f : x → y C
 D... （已译） *)

Definition Full : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y), shom S ox oy f.

(* ... (that is, 含入 函子 D ⟶ C full) （已译） *)

Lemma Full_Implies_Full_Functor : Full → Functor.Full Incl.
Proof.
  unfold Full; intros.
  construct.
  - exists g.
    destruct x, y.
    apply X; auto.
  - reflexivity.
Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Full_sub_iso (full : Full) {x y : C}
        (ox : sobj S x) (oy : sobj S y) (f : x ≅ y) :
  ((x; ox) : Sub) ≅[Sub] (y; oy) := {|
  to   := (to f; full x y ox oy (to f));
  from := (from f; full y x oy ox (from f))
|}.
Next Obligation. apply iso_to_from. Qed.
Next Obligation. apply iso_from_to. Qed.

(*
   本节说明 Subcategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Full_membership_iso (full : Full) (x : C)
        (p q : sobj S x) : ((x; p) : Sub) ≅[Sub] (x; q) := {|
  to   := (id[x]; full x x p q id);
  from := (id[x]; full x x q p id)
|}.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Full_Functor_Implies_Full_upto (HF : Functor.Full Incl) :
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y),
    { g : x ~> y & (g ≈ f) ∧ shom S ox oy g }.
Proof.
  intros x y ox oy f.
  pose (p := @prefmap _ _ Incl HF (x; ox) (y; oy) f).
  exists (`1 p).
  split.
  - exact (@fmap_sur _ _ Incl HF (x; ox) (y; oy) f).
  - exact (`2 p).
Qed.

(*
   本节说明层/筛、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ShomRespects : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f g : x ~> y),
    f ≈ g → shom S ox oy f → shom S ox oy g.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Full_Functor_Implies_Full : ShomRespects → Functor.Full Incl → Full.
Proof.
  intros HR HF x y ox oy f.
  destruct (Full_Functor_Implies_Full_upto HF x y ox oy f) as [g [Hgf Hg]].
  exact (HR _ _ _ _ _ _ Hgf Hg).
Qed.

(* A replete subcategory if any x D any 同构 f : x ≅ y C,
 both y f D. （已译） *)

Definition Replete : Type :=
  ∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
    { oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.

(* A wide subcategory if every object of C is also an object of D. *)

Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.

#[export] Existing Instance Incl_Faithful.
