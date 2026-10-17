(* * * Monoid group actions 函子 范畴 （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/action
 nLab:      https://ncatlab.org/nlab/show/G-set

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Equivariant maps *)

(* A 态射 M-actions: setoid 态射 between carriers
 commuting actions. （已译） *)
Record Equivariant {M : MonObject} (A B : MSetoidAction M) := {
  equiv_map :> act_setoid A ~{Sets}~> act_setoid B;
  equivar : ∀ (g : carrier M) x,
    equiv_map (act A g x) ≈ act B g (equiv_map x)
}.

Arguments equiv_map {M A B} _.
Arguments equivar {M A B} _ _ _.

(** ** The category of M-actions *)

Program Definition MSet (M : MonObject) : Category := {|
  obj := MSetoidAction M;
  hom := fun A B => Equivariant A B;
  homset := fun A B =>
    {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |};
  id := fun A =>
    {| equiv_map := {| morphism := fun x => x |} |};
  compose := fun A B C f g =>
    {| equiv_map := {| morphism := fun x => equiv_map f (equiv_map g x) |} |}
|}.
Next Obligation.
  intros M A B; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x; transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; reflexivity.
Qed.
Next Obligation.
  intros M A B C f g x y Hxy.
  apply (proper_morphism (equiv_map f)).
  apply (proper_morphism (equiv_map g)).
  exact Hxy.
Qed.
Next Obligation.
  intros M A B C f g gr x; simpl.
  rewrite (equivar g gr x).
  apply (equivar f).
Qed.
Next Obligation.
  intros M A B C f f' Hf g g' Hg x; simpl.
  rewrite (Hg x).
  exact (Hf (equiv_map g' x)).
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.

(** ** The comparison functors *)

(* Reading action equivariant maps off 函子: the
 态射 action takes transformation single component,
 whose 自然性 at g IS equivariance. （已译） *)
Program Definition MSet_to (M : MonObject) :
  [Deloop M, Sets] ⟶ MSet M := {|
  fobj := fun F => action_of_functor F;
  fmap := fun F G η =>
    {| equiv_map := transform[η] ttt |}
|}.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F x; simpl; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F G H η θ x; simpl; reflexivity.
Qed.

(* Materializing an equivariant map as the constant transformation
   family; naturality is equivariance. *)
Program Definition MSet_from (M : MonObject) :
  MSet M ⟶ [Deloop M, Sets] := {|
  fobj := fun A => functor_of_action A;
  fmap := fun A B h =>
    {| transform := fun _ => equiv_map h |}
|}.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M A [] x; simpl.
  now rewrite (act_unit A x).
Qed.
Next Obligation.
  intros M A B C f g [] x; simpl; reflexivity.
Qed.

(** ** The equivalence *)

(* The 函子-side round trip, transparent component family
 (the in-tree [action_functor_round] opaque). （已译） *)
Program Definition MSet_round_iso {M : MonObject} (F : Deloop M ⟶ Sets) :
  @Isomorphism ([Deloop M, Sets])
    (functor_of_action (action_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return (functor_of_action (action_of_functor F) x ~{Sets}~> F x)
    with ttt => {| morphism := fun p => p |} end |};
  from := {| transform := fun x =>
    match x return (F x ~{Sets}~> functor_of_action (action_of_functor F) x)
    with ttt => {| morphism := fun p => p |} end |}
|}.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.

(* The action-side round trip: two actions coincide pointwise
 ([action_round] reflexivity), so 恒等 map is
 equivariant both directions. （已译） *)
Program Definition MSet_action_round_iso {M : MonObject}
        (A : MSetoidAction M) :
  @Isomorphism (MSet M) (action_of_functor (functor_of_action A)) A := {|
  to   := {| equiv_map := {| morphism := fun x => x |} |};
  from := {| equiv_map := {| morphism := fun x => x |} |}
|}.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.

(* Mac Lane's 构造 2 at 范畴 strength: 函子
 范畴 over delooped monoid IS 范畴 M-actions, an
 同构 Cat hence (by Cat's convention) 等价
 范畴.（已译） *)
Program Definition MSet_Fun_equiv (M : MonObject) :
  [Deloop M, Sets] ≅[Cat] MSet M := {|
  to   := MSet_to M;
  from := MSet_from M
|}.
Next Obligation.
  (* MSet_to ∘ MSet_from ≈ Id: the action round trip is pointwise
     reflexivity *)
  intros M.
  exists (fun A => MSet_action_round_iso A).
  intros A B h x; simpl; reflexivity.
Qed.
Next Obligation.
  (* MSet_from ∘ MSet_to ≈ Id: the transparent functor-side round trip *)
  intros M.
  exists (fun F => MSet_round_iso F).
  intros F G η [] x; simpl.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)

(* Issue item 2's "unwind", stated literally as hom-setoid
 同构 Sets, following same-directory precedents
 [One_hom_iso] [Discrete_hom_iso]: 自然变换
 between 函子 delooping is exactly one equivariant
 map.（已译） *)
Program Definition MSet_hom_iso {M : MonObject}
        (F G : Deloop M ⟶ Sets) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid (Deloop M) Sets F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := Equivariant (action_of_functor F) (action_of_functor G);
     is_setoid :=
       {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |} |} := {|
  to   := {| morphism := fun η => {| equiv_map := transform[η] ttt |} |};
  from := {| morphism := fun h =>
    {| transform := fun o =>
         match o return (fobj[F] o ~{Sets}~> fobj[G] o) with
         | ttt => equiv_map h
         end |} |}
|}.
Next Obligation.
  intros M F G; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x;
    transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M F G h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F G η [] x; simpl; reflexivity.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition perm_of_group_element {G : GrpObject}
        (F : Deloop G ⟶ FinSet) (g : carrier G) :
  @Isomorphism FinSet (F ttt) (F ttt) :=
  action_automorphism F g.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinPermRep (M : MonObject) : Type :=
  { n : nat & MonHom M (hom_monoid FinSet n) }.

Definition functor_of_perm_rep {M : MonObject} (ρ : FinPermRep M) :
  Deloop M ⟶ FinSet :=
  functor_of_hom_monoid (C := FinSet) (`1 ρ) (`2 ρ).

Definition perm_rep_of_functor {M : MonObject} (F : Deloop M ⟶ FinSet) :
  FinPermRep M :=
  existT (fun n : nat => MonHom M (hom_monoid FinSet n))
    (F ttt : nat) (hom_monoid_of_functor (C := FinSet) F).

(* Over a group, every representation acts by bijections: each element
   goes to an isomorphism of FinSet. *)
Definition perm_rep_acts_by_bijections {G : GrpObject}
        (ρ : FinPermRep G) (g : carrier G) :
  @Isomorphism FinSet (`1 ρ) (`1 ρ) :=
  perm_of_group_element (functor_of_perm_rep ρ) g.
