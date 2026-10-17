Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(** * Presheaves, sites (coverages), and sheaves *)

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
   Where 层 来源, and 用途

   本节说明相关定义、性质与动机。 nLab: https://ncatlab.org/nlab/show/层 nLab: https://ncatlab.org/nlab/show/Grothendieck+topology Wikipedia: https://en.wikipedia.org/wiki/层_(mathematics) A 层 is systematic bookkeeping passage from local data global data.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   A C-valued presheaf on some 范畴 U.

   本节说明相关定义、性质与动机。 C is often taken be Sets. The universe annotation keeps two 范畴' levels independent: left inference, minimization had identified U's hom proof levels C's — one shared level across both 范畴 instances — which Sets target pins elements its

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
  (* A covering family of u is a finite (vector-indexed) list of morphisms
     uᵢ ~> u into u; sigT packages the length together with the vector. *)
  covering_family (u : C) := sigT (Vector.t (∃ uᵢ, uᵢ ~> u));

  (* This encoding picks a single covering family per object rather than the
     usual collection of covering families; it suffices to state the sheaf
     condition below, but is less general than a full coverage. *)
  coverage (u : C) : covering_family u;

  (* The coverage axiom (pullback stability), per the site reference above. *)
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
   If { fᵢ : Uᵢ → U } (i∈I) is a family of 态射 with codomain U,

   本节说明相关定义、性质与动机。 a presheaf X : Cᵒᵖ → Set is called 层 this family if: any collection elements xᵢ ∈ X(Uᵢ) such that, whenever g : V → Uᵢ h : V → Uⱼ are such that fᵢ ∘ g = fⱼ ∘ h, we have X(g)(xᵢ) = X(h)(xⱼ), then there exists unique x ∈ X(U) such that X(fᵢ)(x) = xᵢ all i

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
