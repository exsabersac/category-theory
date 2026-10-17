Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.

Generalizable All Variables.

(* * * Monads 余单子 thin 范畴 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/idempotent+monad
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
   Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Monads in a thin category *)

(* Mac Lane's display (3) in any thin category: an endofunctor with a
   unit family and a multiplication family IS a monad.  Each law is an
   equation between parallel arrows, hence one appeal to [TC]. *)
Definition thin_monad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x) :
  @Monad C T :=
  @Build_Monad C T u m
    (fun _ _ _ => TC _ _ _ _) (fun _ => TC _ _ _ _) (fun _ => TC _ _ _ _)
    (fun _ => TC _ _ _ _) (fun _ _ _ => TC _ _ _ _).

(* 相关说明。 （已译） *)
Example thin_monad_ret@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @ret C T (thin_monad TC T u m) x = u x := eq_refl.

Example thin_monad_join@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @join C T (thin_monad TC T u m) x = m x := eq_refl.

(* Mac Lane p. 141: an algebra is exactly its structure map T x ~> x;
   both algebra laws are thinness. *)
Definition thin_talgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C) :
  @TAlgebra C T MM x ↔ (T x ~> x) :=
  (fun a => @t_alg C T MM x a,
   fun h => @Build_TAlgebra C T MM x h (TC _ _ _ _) (TC _ _ _ _)).

Example thin_talgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C)
  (h : T x ~> x) :
  match thin_talgebra_iff TC (MM := MM) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(* 相关说明。 （已译） *)
Definition thin_join_IsIso@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} (x : C) :
  IsIsomorphism (@join C M MM x) :=
  {| two_sided_inverse := @ret C M MM (M x)
   ; is_right_inverse  := TC _ _ _ _
   ; is_left_inverse   := TC _ _ _ _ |}.

Definition thin_IdempotentMonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} :
  @IdempotentMonad C M MM :=
  {| idem_join_iso := thin_join_IsIso TC |}.

(* * ** The duals, 单子 constants at C^op （已译） *)

(* 相关说明。 （已译） *)
Definition thin_comonad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (W : C ⟶ C) (e : ∀ x : C, W x ~> x) (d : ∀ x : C, W x ~> W (W x)) :
  @Comonad C W :=
  thin_monad (Thin_Opposite TC) (W^op) e d.

(* The 余单子 单子 at C^op nose. （已译） *)
Example thin_comonad_extract@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @extract C W (thin_comonad TC W e d) x = e x := eq_refl.

Example thin_comonad_duplicate@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @duplicate C W (thin_comonad TC W e d) x = d x := eq_refl.

(* Every comonad on a thin category is idempotent: the monad-side
   constant at C^op. *)
Definition thin_IdempotentComonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  IdempotentComonad W H :=
  @thin_IdempotentMonad (C^op) (Thin_Opposite TC) (W^op) H.

(* A coalgebra is exactly an arrow x ~> W x: [thin_talgebra_iff] at C^op,
   read through the bridges of Comonad/Coalgebra.v. *)
Definition thin_wcoalgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C) :
  @WCoalgebra C W H x ↔ (x ~> W x) :=
  let (to_arrow, of_arrow) :=
    thin_talgebra_iff (Thin_Opposite TC) (MM := H) x in
  (fun c => to_arrow (WCoalgebra_to_TAlgebra c),
   fun h => TAlgebra_to_WCoalgebra (of_arrow h)).

Example thin_wcoalgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C)
  (h : x ~> W x) :
  match thin_wcoalgebra_iff TC (H := H) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(* The 含入 counit-fixed 对象 coreflective: dual
 reflection onto closed elements. （已译） *)
Definition thin_coreflective@{t o h s f | h < s +} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  Coreflective@{t t s t f h o h} (WLocal_Subcategory H) :=
  Idempotent_Coreflective H (thin_IdempotentComonad TC).
