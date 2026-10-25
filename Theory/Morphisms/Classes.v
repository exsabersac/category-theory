Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/monomorphism
         https://ncatlab.org/nlab/show/split+monomorphism
         https://ncatlab.org/nlab/show/epimorphism
         https://ncatlab.org/nlab/show/split+epimorphism
         https://ncatlab.org/nlab/show/isomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Morphism

   Classes of morphisms and the inclusions between them. A morphism class on
   a category C assigns to each pair of objects x, y a collection of the
   morphisms x ~> y belonging to the class. The classes collected here —
   monomorphisms, epimorphisms, isomorphisms, split monomorphisms (sections)
   and split epimorphisms (retractions) — sit in the familiar inclusion
   diagram

       Iso ⊆ SplitMono ⊆ Mono
       Iso ⊆ SplitEpi  ⊆ Epi

   with each inclusion witnessed constructively below. As everywhere in this
   library, the laws hold up to the hom-setoid equivalence ≈, never Coq's =.

--------
nLab: https://ncatlab.org/nlab/show/monomorphism
         https://ncatlab.org/nlab/show/split+monomorphism
         https://ncatlab.org/nlab/show/epimorphism
         https://ncatlab.org/nlab/show/split+epimorphism
         https://ncatlab.org/nlab/show/isomorphism
   维基百科: https://en.wikipedia.org/wiki/Morphism

   态射类及其包含关系。一个范畴 C 上的态射类为每一对对象 x, y 分配一个属于该类的态射 x ~> y 的集合。此处收集的类——单射、满射、同构、分裂单射（截）和分裂满射（重traction）——位于熟悉的包含图中：

       Iso ⊆ SplitMono ⊆ Mono
       Iso ⊆ SplitEpi  ⊆ Epi

   每个包含关系在下面都有构造性的证明。如同本库中的其他地方一样，这些规律在同态集等价 ≈ 下成立，而不是 Coq 的 =。
*)

Definition MorphismClass (C : Category) := ∀ x y : C, (x ~> y) → Type.

(* The class of monomorphisms: left-cancellable morphisms. / 单态射的类：可左消去的态射。 *)
Definition MonoClass {C : Category} : MorphismClass C :=
  fun _ _ f => Monic f.

(* The class of epimorphisms: right-cancellable morphisms. / 满射的类：右可消的态射。 *)
Definition EpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => Epic f.

(* The class of isomorphisms: morphisms with a two-sided inverse. / 同构的范畴：具有双向逆的态射。 *)
Definition IsoClass {C : Category} : MorphismClass C :=
  fun _ _ f => IsIsomorphism f.

(* The class of split monomorphisms: morphisms with a left inverse. / 分裂单态的类：具有左逆的态射。 *)
Definition SplitMonoClass {C : Category} : MorphismClass C :=
  fun _ _ f => Section f.

(* The class of split epimorphisms: morphisms with a right inverse. / 分裂自射的类：具有右逆的态射。 *)
Definition SplitEpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => Retraction f.

(* Every split monomorphism is a monomorphism. / 每个分裂单射都是单射。 *)
Lemma split_mono_in_mono {C : Category} {x y : C} (f : x ~> y) :
  SplitMonoClass x y f → MonoClass x y f.
Proof.
  exact (sections_are_monic x y f).
Qed.

(* Every split epimorphism is an epimorphism. / 每个分裂的满射都是满射。 *)
Lemma split_epi_in_epi {C : Category} {x y : C} (f : x ~> y) :
  SplitEpiClass x y f → EpiClass x y f.
Proof.
  exact (retractions_are_epic x y f).
Qed.

(*
An isomorphism is a split monomorphism: its two-sided inverse serves as a
   left inverse.

--------
同构是一个分裂单态：它的双边逆作为左逆。
*)
Lemma iso_in_split_mono {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → SplitMonoClass x y f.
Proof.
  intros iso.
  exact (@Build_Section C x y f
           (@two_sided_inverse C x y f iso)
           (@is_left_inverse C x y f iso)).
Qed.

(*
An isomorphism is a split epimorphism: its two-sided inverse serves as a
   right inverse.

--------
同构是一个分裂的满射：它的双边逆元可以作为右逆元。
*)
Lemma iso_in_split_epi {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → SplitEpiClass x y f.
Proof.
  intros iso.
  exact (@Build_Retraction C x y f
           (@two_sided_inverse C x y f iso)
           (@is_right_inverse C x y f iso)).
Qed.

(* Every isomorphism is a monomorphism, through its splitting. / 每一个同构都是单射，通过它的分裂。 *)
Lemma iso_in_mono {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → MonoClass x y f.
Proof.
  intros iso.
  exact (split_mono_in_mono f (iso_in_split_mono f iso)).
Qed.

(* Every isomorphism is an epimorphism, through its splitting. / 每一个同构都是一个满射，通过其分裂实现。 *)
Lemma iso_in_epi {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → EpiClass x y f.
Proof.
  intros iso.
  exact (split_epi_in_epi f (iso_in_split_epi f iso)).
Qed.
