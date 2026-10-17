(* ========================================================================= *)
(* Regression suite for issue #138.                                          *)
(*                                                                           *)
(* 相关说明。 （已译） *)
(*                                                                           *)
(*   - [StrictCat] is the STRICT category of categories: its homset          *)
(*     equivalence is [Functor_StrictEq_Setoid] (strict equality of          *)
(*     functors), not the weak nat-iso equivalence [Functor_Setoid] used by  *)
(*     the weak category [Cat].                                              *)
(*                                                                           *)
(* - The underlying-graph [Forgetful] 函子 [Free] ⊣ [Forgetful] （已译） *)
(*     adjunction live OVER [StrictCat], not over the weak [Cat].  They       *)
(*     cannot be defined over [Cat] because they do not respect natural      *)
(*     isomorphism: a category's underlying quiver is not invariant under     *)
(* the weak 等价 [Cat]'s [Functor_Setoid] identifies. （已译） *)
(*                                                                           *)
(* - The comparison 函子 [StrictCat_to_Cat] witnesses strict （已译） *)
(*     equality of functors implies natural isomorphism (strict-eq ⟹         *)
(*     natural-iso), exhibiting [StrictCat] as a refinement of [Cat].        *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Free.Quiver.
Generalizable All Variables.

(* ===== BLOCK A138 — forgetful behaviour ===== *)

(*
   本文件为测试：Issue138。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Check (Forgetful : StrictCat ⟶ QuiverCategory).

(* Computational behaviour: underlying nodes 范畴's 对象. （已译） *)
Example A138_nodes (C : Category) : @nodes (Forgetful C) = obj[C] := eq_refl.

(* 相关说明。 （已译） *)
Example A138_edges (C : Category) (x y : C) :
  @edges (Forgetful C) x y = (x ~> y) := eq_refl.

(* The edge-map 函子's fmap 函子's fmap. （已译） *)
Example A138_fedgemap (C D : Category) (F : C ⟶ D) (x y : C) (f : x ~> y) :
  @fedgemap _ _ (fmap[Forgetful] F) x y f = fmap[F] f := eq_refl.

(* The underlying constructions 对象 态射 well-typed. （已译） *)
Check (QuiverOfCat : Category -> Quiver).
Check (@QuiverHomomorphismOfFunctor
        : ∀ (C D : Category), (C ⟶ D) ->
            QuiverHomomorphism (QuiverOfCat C) (QuiverOfCat D)).

(* The composite Forgetful ◯ FreeCatFunctor is an endofunctor on QuiverCategory. *)
Check (Forgetful ◯ FreeCatFunctor : QuiverCategory ⟶ QuiverCategory).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Forgetful : Cat ⟶ QuiverCategory).
Fail Definition A138_forgetful_over_Cat : Cat ⟶ QuiverCategory := Forgetful.

(* ===== BLOCK B138 — free ⊣ forgetful adjunction ===== *)

Check (FreeCatFunctor : QuiverCategory ⟶ StrictCat).

Check (FreeForgetfulAdjunction : FreeCatFunctor ⊣ Forgetful).

(* A concrete worked quiver: one node, one loop.
 NB: bare [unit] edge position resolves 伴随-unit notation, so
 we must qualify Coq type [Datatypes.unit]. （已译） *)
Definition B138_loop : Quiver :=
  Build_Quiver_Standard_Eq Datatypes.unit (fun _ _ => Datatypes.unit).

Check (FreeOnQuiver B138_loop : Category).
Check (FreeCatFunctor B138_loop : Category).

(* The nodes free 范畴 loop quiver exactly quiver's
 nodes (here [unit]). （已译） *)
Example B138_free_loop_nodes :
  obj[FreeOnQuiver B138_loop] = Datatypes.unit := eq_refl.

(* The composite endofunctor on StrictCat *)
Check (FreeCatFunctor ◯ Forgetful : StrictCat ⟶ StrictCat).

(* ===== BLOCK C138 — StrictCat strict laws ===== *)

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example C138_homset_is_strict (A B : Category) :
  @homset StrictCat A B = @Functor_StrictEq_Setoid A B := eq_refl.

(* The strict identity law, exercised through StrictCat's OWN category structure
   (its [id], [compose], [homset] and [id_left]), rather than only via the
   free-standing [fun_strict_equiv_*] lemmas. *)
Example C138_strictcat_id_left (A B : Category) (F : A ⟶ B) :
  @equiv _ (@homset StrictCat A B)
         (@compose StrictCat _ _ _ (@id StrictCat B) F) F :=
  @id_left StrictCat A B F.

(* The three strict 范畴 laws, stated EXPLICIT strict setoid
 discharged existing lemmas. （已译） *)
Example C138_id_left {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F := fun_strict_equiv_id_left F.

Example C138_id_right {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ Id) F := fun_strict_equiv_id_right F.

Example C138_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ (G ◯ H)) ((F ◯ G) ◯ H) :=
  fun_strict_equiv_comp_assoc F G H.

(* Strict equality is genuinely an equivalence usable on concrete witnesses. *)

(* Reflexivity of a functor under the strict setoid. *)
Example C138_strict_refl {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid F F.
Proof.
  reflexivity.
Qed.

(* Id ◯ (Id ◯ F) relates to F under strict equality, using transitivity. *)
Example C138_nested_id {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ (Id ◯ F)) F.
Proof.
  transitivity (Id ◯ F).
  - exact (fun_strict_equiv_id_left (Id ◯ F)).
  - exact (fun_strict_equiv_id_left F).
Qed.

(* Strict equality refines weak (nat-iso) equality. *)
Example C138_strict_refines_weak {A B} (F : A ⟶ B) :
  @equiv _ Functor_Setoid (Id ◯ F) F :=
  strict_equiv_implies_fun_equiv (Id ◯ F) F (fun_strict_equiv_id_left F).

(* ===== BLOCK D138 — comparison functor ===== *)

Check (StrictCat_to_Cat : StrictCat ⟶ Cat).

Example D138_obj (C : Category) : StrictCat_to_Cat C = C := eq_refl.

Example D138_map {C D} (F : C ⟶ D) : fmap[StrictCat_to_Cat] F = F := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example D138_iso_of_eq_refl_to (C : Category) (x : C) :
  to (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_iso_of_eq_refl_from (C : Category) (x : C) :
  from (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_strict_to_weak {C D} (F G : C ⟶ D)
  (H : @equiv _ Functor_StrictEq_Setoid F G) : @equiv _ Functor_Setoid F G
  := strict_equiv_implies_fun_equiv F G H.

(* Concrete instance: re-derive a strict equality witness locally (id_left),
   then push it through the comparison functor to obtain a weak (nat-iso)
   equality in Cat. *)

Definition D138_idleft_strict {C D} (F : C ⟶ D)
  : @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F
  := fun_strict_equiv_id_left F.

Definition D138_idleft_weak {C D} (F : C ⟶ D)
  : @equiv _ Functor_Setoid (Id ◯ F) F
  := strict_equiv_implies_fun_equiv (Id ◯ F) F (D138_idleft_strict F).
