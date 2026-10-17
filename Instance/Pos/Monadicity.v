Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Identity.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Proset.Monotone.

Generalizable All Variables.

(* * * The discrete-poset 伴随: 恒等 单子 over propositional
 setoids, truncation 单子 over [Sets], [Pos_Forget] not
 monadic （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/propositional+truncation

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition pos_PropEquiv@{w c cp p0 p1 p2 p3 |
  Set < w, Set < p2, c <= w, cp <= w, c <= p0, c <= p1, cp <= p1,
  p2 <= p0, p3 <= p1}
  (P : PosetObject@{c cp p0 p1 p2 p3}) :
  PropEquivObj@{w c cp} (pos_setoid P).
Proof.
  unshelve refine {| pequiv := fun x y => pos_le P x y /\ pos_le P y x |}.
  - intros x y [H1 H2]. exact (pos_antisym P x y H1 H2).
  - intros x y E. split.
    + apply (proj1 (pos_le_respects P x x (reflexivity x) x y E)).
      apply pos_refl.
    + apply (proj1 (pos_le_respects P x y E x x (reflexivity x))).
      apply pos_refl.
Defined.

Definition PosPForget@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Pos@{po p0 p1 p2 p3 c} ⟶ PropSets@{c so} :=
  PropSets_lift@{po c c so} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

Example Pos_Forget_factor_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (P : Pos@{po p0 p1 p2 p3 c}) :
  fobj[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] P
    = fobj[Pos_Forget@{po so p0 p2 p1 p3 c}] P := eq_refl.

Example Pos_Forget_factor_map@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (P Q : Pos@{po p0 p1 p2 p3 c}) (f : P ~{Pos@{po p0 p1 p2 p3 c}}~> Q) :
  fmap[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] f
    = fmap[Pos_Forget@{po so p0 p2 p1 p3 c}] f := eq_refl.

Definition Pos_Forget_factor@{c so po p0 p1 p2 p3 s a b |
  c < so, c < s, c < b, po <= a, po <= b, c <= a, so <= a, c < po, Set < p2,
  p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @equiv _ (@Functor_Setoid@{a b po s so c} Pos@{po p0 p1 p2 p3 c} Sets@{c so})
    (PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3})
    Pos_Forget@{po so p0 p2 p1 p3 c} :=
  PropSets_lift_Incl@{po c so s a b} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

(* 相关说明。 （已译） *)

Definition PosDiscPObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) : PosetObject@{c c p0 p1 p2 p3} := {|
  pos_setoid := projT1 X;
  pos_le := @pequiv _ _ (projT2 X);
  pos_le_respects := @pequiv_Proper _ _ (projT2 X);
  pos_refl := fun x => pequiv_from x x (reflexivity x);
  pos_trans := fun x y z H K =>
    pequiv_from x z (transitivity (pequiv_to x y H) (pequiv_to y z K));
  pos_antisym := fun x y H _ => pequiv_to x y H
|}.

Definition PosDiscP_fmap@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X Y : PropSets@{c so}} (f : X ~{PropSets@{c so}}~> Y) :
  MonoHom@{p0 p1 p2 p3 p1 p3 c} (PosDiscPObj@{c so p0 p1 p2 p3} X)
    (PosDiscPObj@{c so p0 p1 p2 p3} Y).
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X)
            (PosDiscPObj@{c so p0 p1 p2 p3} Y) (projT1 f) _).
  intros x y H. simpl in *.
  exact (pequiv_from _ _ (proper_morphism (projT1 f) x y (pequiv_to x y H))).
Defined.

Definition PosDiscP@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PropSets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor PropSets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscPObj@{c so p0 p1 p2 p3}
                     (fun X Y f => PosDiscP_fmap@{c so p0 p1 p2 p3} f)
                     _ _ _).
  - intros X Y f g E x. exact (E x).
  - intros X x. simpl. reflexivity.
  - intros X Y Z f g x. simpl. reflexivity.
Defined.

Definition posdiscP_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P) :
  PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X) P (projT1 g) _).
  intros x y H. simpl in *.
  apply (proj1 (pos_le_respects P (projT1 g x) (projT1 g x) (reflexivity _)
                  (projT1 g x) (projT1 g y)
                  (proper_morphism (projT1 g) x y (pequiv_to x y H)))).
  apply pos_refl.
Defined.

Definition posdiscP_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P.
Proof. exists (mono_fn k). exact I. Defined.

#[local] Obligation Tactic := idtac.

Program Definition posdiscP_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDiscP@{c so po p0 p1 p2 p3} X) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDiscP@{c so po p0 p1 p2 p3} X) P |}
    {| carrier := @hom PropSets@{c so} X
                    (PosPForget@{c so po p0 p1 p2 p3} P) ;
       is_setoid := @homset PropSets@{c so} X
                      (PosPForget@{c so po p0 p1 p2 p3} P) |} := {|
  to   := {| morphism := fun k => posdiscP_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdiscP_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros X P k k' H x; exact (H x). Qed.
Next Obligation. intros X P g g' H x; exact (H x). Qed.
Next Obligation. intros X P g x; reflexivity. Qed.
Next Obligation. intros X P k x; reflexivity. Qed.

Definition PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} PropSets@{c so}
    PosDiscP@{c so po p0 p1 p2 p3} PosPForget@{c so po p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDiscP@{c so po p0 p1 p2 p3}
                     PosPForget@{c so po p0 p1 p2 p3}
                     posdiscP_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* * ** Over [PropSets] induced 单子 恒等 单子 （已译） *)

Definition TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets@{c so} ⟶ PropSets@{c so} :=
  PosPForget@{c so po p0 p1 p2 p3} ◯ PosDiscP@{c so po p0 p1 p2 p3}.

Definition MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad PropSets@{c so} TPosP@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a}.

Example TPosP_setoid@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X) = projT1 X := eq_refl.

Example TPosP_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X Y : PropSets@{c so}) (f : X ~{PropSets@{c so}}~> Y) :
  projT1 (fmap[TPosP@{c so po p0 p1 p2 p3 s}] f) = projT1 f := eq_refl.

Example TPosP_pequiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) (x y : carrier (projT1 X)) :
  @pequiv _ _ (projT2 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X)) x y
    = (@pequiv _ _ (projT2 X) x y /\ @pequiv _ _ (projT2 X) y x)
  := eq_refl.

Example MPosP_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@ret _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Example MPosP_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@join _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Definition TPosP_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPosP@{c so po p0 p1 p2 p3 s} ⟹ Id[PropSets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPosP@{c so po p0 p1 p2 p3 s})
                     (G:=Id[PropSets@{c so}]) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition id_to_TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[PropSets@{c so}] ⟹ TPosP@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[PropSets@{c so}])
                     (G:=TPosP@{c so po p0 p1 p2 p3 s}) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition MPosP_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPosP@{c so po p0 p1 p2 p3 s a}
    (IdMonad@{so c} PropSets@{c so}).
Proof.
  unshelve refine {| mh_transform := TPosP_to_id@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition Id_to_MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} PropSets@{c so})
    MPosP@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPosP@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Example MPosP_to_Id_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform MPosP_to_Id@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Example Id_to_MPosP_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform Id_to_MPosP@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Definition MPosP_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so}))
    MPosP_to_Id@{c so po p0 p1 p2 p3 s a}
    Id_to_MPosP@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; reflexivity.
Defined.

(* Awodey's "Eilenberg-Moore 范畴 T = 1_Sets then just Sets
 itself", over [PropSets]: Monad/Identity.v's [IdMonad_EM_equivalence]
 at [PropSets]. （已译） *)
Definition PropSets_EM_Id_equivalence@{c so s e | c < so, c < s, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so c s e} PropSets@{c so} Id[PropSets@{c so}]
       (IdMonad@{so c} PropSets@{c so})) :=
  IdMonad_EM_equivalence@{so c s e} PropSets@{c so}.

(* 相关说明。 （已译） *)

Definition PosDiscObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} (S : Sets@{c so}) :
  PosetObject@{c c p0 p1 p2 p3} :=
  PosDiscPObj@{c so p0 p1 p2 p3} (PropSets_trunc@{c so} S).

Example PosDiscObj_le@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  pos_le (PosDiscObj@{c so p0 p1 p2 p3} S) x y = inhabited (x ≈ y)
  := eq_refl.

Definition PosDisc@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor Sets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscObj@{c so p0 p1 p2 p3}
                     (fun S T f => PosDiscP_fmap@{c so p0 p1 p2 p3}
                                     (fmap[PropSets_trunc@{c so}] f))
                     _ _ _).
  - intros S T f g E x. exact (inhabits (E x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

Example PosDisc_obj@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) :
  fobj[PosDisc@{c so po p0 p1 p2 p3}] S
    = fobj[PosDiscP@{c so po p0 p1 p2 p3}] (fobj[PropSets_trunc@{c so}] S)
  := eq_refl.

Example PosDisc_map@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[PosDisc@{c so po p0 p1 p2 p3}] f
    = fmap[PosDiscP@{c so po p0 p1 p2 p3}] (fmap[PropSets_trunc@{c so}] f)
  := eq_refl.

Definition posdisc_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P) :
  PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  unshelve refine (@Build_MonoHom (PosDiscObj@{c so p0 p1 p2 p3} S) P
                     (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _) _).
  - intros x y H. simpl in *.
    apply (@pequiv_elim_inhabited _ _ (pos_PropEquiv@{so c c p0 p1 p2 p3} P)).
    destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
  - intros x y H. simpl in *. destruct H as [H].
    apply (proj1 (pos_le_respects P (g x) (g x) (reflexivity _) (g x) (g y)
                    (proper_morphism g x y H))).
    apply pos_refl.
Defined.

Definition posdisc_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => mono_fn k x) _).
  intros x y H. exact (proper_morphism (mono_fn k) x y (inhabits H)).
Defined.

Program Definition posdisc_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDisc@{c so po p0 p1 p2 p3} S) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDisc@{c so po p0 p1 p2 p3} S) P |}
    {| carrier := @hom Sets@{c so} S (Pos_Forget@{po so p0 p2 p1 p3 c} P) ;
       is_setoid := @homset Sets@{c so} S
                      (Pos_Forget@{po so p0 p2 p1 p3 c} P) |} := {|
  to   := {| morphism := fun k => posdisc_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdisc_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros S P k k' H x; exact (H x). Qed.
Next Obligation. intros S P g g' H x; exact (H x). Qed.
Next Obligation. intros S P g x; reflexivity. Qed.
Next Obligation. intros S P k x; reflexivity. Qed.

Definition PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} Sets@{c so}
    PosDisc@{c so po p0 p1 p2 p3} Pos_Forget@{po so p0 p2 p1 p3 c}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDisc@{c so po p0 p1 p2 p3}
                     Pos_Forget@{po so p0 p2 p1 p3 c}
                     posdisc_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* * ** Over [Sets] induced 单子 truncation 单子 （已译） *)

Definition TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Sets@{c so} ⟶ Sets@{c so} :=
  Pos_Forget@{po so p0 p2 p1 p3 c} ◯ PosDisc@{c so po p0 p1 p2 p3}.

Definition MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad Sets@{c so} TPos@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a}.

Example TPos_fobj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  fobj[TPos@{c so po p0 p1 p2 p3 s}] S
    = fobj[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] S := eq_refl.

Example TPos_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[TPos@{c so po p0 p1 p2 p3 s}] f
    = fmap[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] f := eq_refl.

Example TPos_carrier@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  carrier (fobj[TPos@{c so po p0 p1 p2 p3 s}] S) = carrier S := eq_refl.

Example TPos_equiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  @equiv _ (is_setoid (fobj[TPos@{c so po p0 p1 p2 p3 s}] S)) x y
    = inhabited (x ≈ y) := eq_refl.

Example MPos_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@ret _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Example MPos_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@join _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Definition TPos_to_trunc@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}.
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets_Incl@{c so} ◯ PropSets_trunc@{c so} ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform'
                     (F:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition MPos_to_trunc@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
    (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}).
Proof.
  unshelve refine {| mh_transform := TPos_to_trunc@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_MPos@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})
    MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := trunc_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition MPos_trunc_iso@{c so po p0 p1 p2 p3 s a r m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}))
    MPos_to_trunc@{c so po p0 p1 p2 p3 s a r}
    trunc_to_MPos@{c so po p0 p1 p2 p3 s a r} _ _);
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

(* * ** Over [Sets], induced 单子 恒等 （已译） *)

Definition id_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[Sets@{c so}] ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{c so}])
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (inhabits H).
  - intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition Id_to_MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} Sets@{c so}) MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition SetsTruncElim@{c so | c < so +} : Type@{so} :=
  ∀ (S : Sets@{c so}) (x y : carrier S), inhabited (x ≈ y) → x ≈ y.

Lemma MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (θ : MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
         (IdMonad@{so c} Sets@{c so})) : SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  exact (@proper_morphism _ _ _ _ (transform[mh_transform θ] S) x y H).
Qed.

Definition TPos_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ Id[Sets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=Id[Sets@{c so}]) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (Htrunc S x y H).
  - intros S T f x; simpl. reflexivity.
Defined.

Definition MPos_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a} (IdMonad@{so c} Sets@{c so}).
Proof.
  unshelve refine
    {| mh_transform := TPos_to_id@{c so po p0 p1 p2 p3 s} Htrunc |};
    intros x z; simpl; reflexivity.
Defined.

Definition MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (Htrunc : SetsTruncElim@{c so}) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so}))
    (MPos_to_Id@{c so po p0 p1 p2 p3 s a} Htrunc)
    Id_to_MPos@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; [ reflexivity | exact (inhabits (reflexivity _)) ].
Defined.

(*
   本节说明 Monadicity 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition choice_setoid@{c | +} (A : Type@{c}) : SetoidObject@{c c} :=
  SquashSetoid@{c} A.

(*
   本节说明 Monadicity 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma trunc_choice@{c so | c < so +} (Htrunc : SetsTruncElim@{c so})
  (A : Type@{c}) : inhabited A → A.
Proof.
  intros H.
  destruct (Htrunc (choice_setoid@{c} A) true false
              (match H with inhabits a => inhabits (inr a) end)) as [e|a].
  - exact (match Bool.diff_true_false e with end).
  - exact a.
Qed.

Lemma choice_trunc@{c so | c < so +}
  (G : ∀ A : Type@{c}, inhabited A → A) : SetsTruncElim@{c so}.
Proof. intros S x y. exact (G (x ≈ y)). Qed.

Definition MPos_Id_iff@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  iffT (@Isomorphism (Monads@{so c m1 m2} Sets@{c so})
          (existT _ TPos@{c so po p0 p1 p2 p3 s}
             MPos@{c so po p0 p1 p2 p3 s a})
          (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})))
       (∀ A : Type@{c}, inhabited A → A).
Proof.
  split.
  - intros Hiso.
    exact (trunc_choice@{c so}
             (MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a} (to Hiso))).
  - intros G.
    exact (MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
             (choice_trunc@{c so} G)).
Defined.

(* A [PropEquiv] on every object of [Sets] is the principle again, in both
   directions. *)
Definition all_PropEquiv_trunc@{c so | c < so +}
  (P : ∀ X : Sets@{c so}, PropEquivObj@{so c c} X) : SetsTruncElim@{c so} :=
  fun S x y H => @pequiv_elim_inhabited _ _ (P S) x y H.

Definition trunc_all_PropEquiv@{c so | c < so +}
  (T : SetsTruncElim@{c so}) (X : Sets@{c so}) : PropEquivObj@{so c c} X :=
  @PropEquiv_of_relation (carrier X) (is_setoid X)
    (fun x y => inhabited (x ≈ y)) (fun x y H => T X x y H)
    (fun x y H => inhabits H).

(*
   本节说明伴随、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma any_adj_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (F : Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c})
  (A : @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c}
         Sets@{c so} F Pos_Forget@{po so p0 p2 p1 p3 c})
  (θ : MonadHom@{so c}
         (@Adjunction_Induced_Monad@{po c so c so a s} _ _ _ _ A)
         (IdMonad@{so c} Sets@{c so})) :
  SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  apply (@proper_morphism _ _ _ _ (transform[mh_transform θ] S)).
  apply (@pequiv_elim_inhabited _ _
           (pos_PropEquiv@{so c c p0 p1 p2 p3} (F S))).
  destruct H as [H]. constructor.
  exact (@proper_morphism _ _ _ _
           (@ret _ _ (Adjunction_Induced_Monad A) S) x y H).
Qed.

(*
   本节说明 Monadicity 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition choice_of_IEM@{c | +} (E : ∀ P : Type@{c}, P + (P → False)) :
  ∀ A : Type@{c}, inhabited A → A :=
  fun A h => match E A with
             | inl a => a
             | inr N => match (match h with inhabits a => N a end) with end
             end.

(* Under informative excluded middle induced 单子 IS 恒等
 单子, up 同构 [Monads Sets]. （已译） *)
Definition MPos_IEM_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (E : ∀ P : Type@{c}, P + (P → False)) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})) :=
  MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
    (choice_trunc@{c so} (choice_of_IEM@{c} E)).

(** ** Not monadic *)

Lemma bool_le_antisym@{} (x y : bool) :
  bool_le x y → bool_le y x → x = y.
Proof.
  destruct x, y; unfold bool_le; intros H K; try reflexivity.
  - exact (eq_sym (H eq_refl)).
  - exact (K eq_refl).
Qed.

Definition BoolDiscPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  : PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} (@eq bool)
                     _ (fun x => eq_refl) (fun x y z H1 H2 => eq_trans H1 H2)
                     (fun x y H _ => H)).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition BoolChainPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} bool_le
                     _ (fun x H => H) (fun x y z H K e => K (H e))
                     bool_le_antisym).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition bool_disc_to_chain@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  BoolDiscPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
    BoolChainPos@{c p0 p1 p2 p3}.
Proof.
  refine (@Build_MonoHom BoolDiscPos@{c p0 p1 p2 p3}
            BoolChainPos@{c p0 p1 p2 p3} setoid_morphism_id _).
  intros x y H e. cbn in H. destruct H. exact e.
Defined.

Lemma no_bool_chain_to_disc@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (g : BoolChainPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
         BoolDiscPos@{c p0 p1 p2 p3}) :
  (∀ b : bool, mono_fn g b = b) → False.
Proof.
  intros Hg.
  assert (H : mono_fn g false = mono_fn g true)
    by (apply (mono_le g); intro e; discriminate e).
  rewrite (Hg false), (Hg true) in H. discriminate H.
Qed.

Lemma Pos_Forget_not_Full@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Functor.Full Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros HF.
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
           BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id b).
Qed.

Lemma Pos_Forget_not_ReflectsIsos@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  ReflectsIsos Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{c so} _ _
                 (fmap[Pos_Forget@{po so p0 p2 p1 p3 c}]
                    bool_disc_to_chain@{c po p0 p1 p2 p3})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3} g). intro b. exact (Hr b).
Qed.

Lemma Pos_Forget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Lemma PosPForget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} PosPForget@{c so po p0 p1 p2 p3} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism PropSets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor;
      [ exists setoid_morphism_id; exact I | intro b; reflexivity
      | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (projT1 (t_alg_hom[g]) b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Definition PropSets_Incl_Monadic@{c so r m m1 m3 |
  c < so, so <= m1, so <= m3, c <= m1, c <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m so m1 so m3 c so r} PropSets_Incl@{c so} :=
  Reflective_Monadic PropSets_Reflective@{c so r}.
