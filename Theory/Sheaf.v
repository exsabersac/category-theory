Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* nLab: https://ncatlab.org/nlab/show/presheaf
   Wikipedia: https://en.wikipedia.org/wiki/Presheaf_(category_theory)

   范畴 U 上取值于 C 的预层 (presheaf) 是函子 U^op ⟶ C；经典情形取 C := Sets。
   其对 U 的态射 f : a ~> b 的作用 fmap[X] f 是限制映射 X(b) → X(a)。U 上的预层
   构成函子范畴 [U^op, C]；余预层 (copresheaf) 是共变变体 U ⟶ C（即 U^op 上的预层）。 *)

(* nLab: https://ncatlab.org/nlab/show/site
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_topology

   位 (site) 是配备 Grothendieck 拓扑的范畴：对每个对象指定覆盖筛，服从稳定性与局部性公理。 *)

(* nLab: https://ncatlab.org/nlab/show/sheaf
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   层 (sheaf) 是满足下降条件的预层：对拓扑中的每个覆盖，截面由兼容的局部截面唯一胶合。 *)

(*
   关于sheaves的来源与用途

   nLab:      https://ncatlab.org/nlab/show/sheaf
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+topology
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   本节说明层/筛、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Presheaf@{u1 u2 u3 u4 u5 u6 +}
  (U : Category@{u1 u2 u3}) (C : Category@{u4 u5 u6}) := U^op ⟶ C.

(* The category of C-valued presheaves on a category U. *)
Definition Presheaves {U C : Category} := [U^op, C].

(* A C-valued copresheaf on U: a covariant functor, i.e. a presheaf on U^op. *)
Definition Copresheaf (U C : Category) := U ⟶ C.

(* The category of C-valued copresheaves on a category U. *)
Definition Copresheaves {U C : Category} := [U, C].

(* Custom data type to express Forall propositions on vectors over Type. *)
Inductive ForallT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ForallT_nil : ForallT (nil A)
  | ForallT_cons (n : nat) (x : A) (v : t A n) :
    P x → ForallT v → ForallT (cons A x n v).

(* Likewise the Type-valued analogue of Vector.Exists, carrying witness data. *)
Inductive ExistsT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ExistsT_cons_hd (m : nat) (x : A) (v : t A m) :
    P x → ExistsT (cons A x m v)
  | ExistsT_cons_tl (m : nat) (x : A) (v : t A m) :
    ExistsT v → ExistsT (cons A x m v).

(* A coverage on a category C consists of a function assigning to each object
   U ∈ C a collection of families of morphisms { fᵢ : Uᵢ → U } (i∈I), called
   covering families, such that

   if { fᵢ : Uᵢ → U } (i∈I) is a covering family
   and g : V → U is a morphism,
   then there exists a covering family { hⱼ : Vⱼ → V }
   such that each composite g ∘ hⱼ factors through some fᵢ. *)

Class Site (C : Category) := {
  (* A covering family u finite (vector-indexed) list 态射
 uᵢ ~> u u; sigT packages length together vector. （已译） *)
  covering_family (u : C) := sigT (Vector.t (∃ uᵢ, uᵢ ~> u));

  (* This encoding picks a single covering family per object rather than the
     usual collection of covering families; it suffices to state the sheaf
     condition below, but is less general than a full coverage. *)
  coverage (u : C) : covering_family u;

  (* 相关说明。 （已译） *)
  coverage_condition
    (u  : C) (fs : covering_family u)
    (v  : C) (g  : v ~> u) :
    ∃ hs : covering_family v,
      ForallT (A := ∃ vⱼ, vⱼ ~> v) (λ '(vⱼ; hⱼ),
          ExistsT (A := ∃ uᵢ, uᵢ ~> u) (λ '(uᵢ; fᵢ),
              ∃ k : vⱼ ~> uᵢ, fᵢ ∘ k ≈ g ∘ hⱼ)
            (`2 fs))
        (`2 hs)
}.

(*
   本节说明层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Sheaf `{@Site C} (X : Presheaf C Sets) := {
  restriction :
    ∀ u : C,
      let '(i; f) := coverage u in
      ForallT
        (A := ∃ uᵢ, uᵢ ~> u)
        (λ '(uᵢ; fᵢ),
            ∀ xᵢ : X uᵢ,
              (∀ (v : C) (g : v ~> uᵢ),
                  ForallT
                    (A := ∃ uⱼ, uⱼ ~> u)
                    (λ '(uⱼ; fⱼ),
                      ∀ h : v ~> uⱼ,
                        fᵢ ∘ g ≈ fⱼ ∘ h →
                        ∀ xⱼ : X uⱼ,
                          fmap[X] g xᵢ ≈ fmap[X] h xⱼ)
                    f) →
              ∃! x : X u, fmap[X] fᵢ x ≈ xᵢ)
        f
}.
