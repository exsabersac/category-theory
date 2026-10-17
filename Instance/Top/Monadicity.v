Require Import Category.Lib.
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
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.

Generalizable All Variables.

(* * * The discrete-space 伴随 induces 恒等 单子, not
 monadic （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/discrete+space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The induced monad *)

(* 相关说明。 （已译） *)
Definition PDiscT@{o so s | o < so, o < s +} :
  Sets@{o so} ⟶ Sets@{o so} :=
  PForget@{o so} ◯ PDisc@{o so}.

Definition PDiscMonad@{o so s u u0 | o < so, o < s, o < u +} :
  @Monad Sets@{o so} PDiscT@{o so s} :=
  @Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}.

Example PDiscT_fobj@{o so s | o < so, o < s +} (x : Sets@{o so}) :
  fobj[PDiscT@{o so s}] x = x := eq_refl.

Example PDiscT_fmap@{o so s | o < so, o < s +} (x y : Sets@{o so})
  (f : x ~> y) : fmap[PDiscT@{o so s}] f = f := eq_refl.

Example PDisc_PForget_unit@{o so u u0 | o < so, o < u +}
  (x : Sets@{o so}) :
  @unit _ _ _ _ PDisc_PForget@{o so u u0} x = id := eq_refl.

Example PDisc_PForget_counit@{o so u u0 | o < so, o < u +}
  (X : PTopCat@{o so}) :
  pmap (@counit _ _ _ _ PDisc_PForget@{o so u u0} X) = setoid_morphism_id
  := eq_refl.

Example PDiscMonad_ret@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @ret _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

Example PDiscMonad_join@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @join _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

(* The data fields 函子 单子, functions: I = ⟨I,
 1, 1⟩ nose. （已译） *)
Example PDiscT_fields@{o so s | o < so, o < s +} :
  (@fobj _ _ PDiscT@{o so s}, @fmap _ _ PDiscT@{o so s})
    = (@fobj _ _ Id[Sets@{o so}], @fmap _ _ Id[Sets@{o so}]) := eq_refl.

Example PDiscMonad_fields@{o so s u u0 | o < so, o < s, o < u +} :
  (@ret _ _ PDiscMonad@{o so s u u0}, @join _ _ PDiscMonad@{o so s u u0})
    = (@ret _ _ (IdMonad@{so o} Sets@{o so}),
       @join _ _ (IdMonad@{so o} Sets@{o so})) := eq_refl.

(* * ** The 同构 恒等 单子, [Monads Sets] （已译） *)

Definition disc_to_id@{o so s | o < so, o < s +} :
  PDiscT@{o so s} ⟹ Id[Sets@{o so}].
Proof.
  unshelve refine (Build_Transform' (F:=PDiscT@{o so s})
                     (G:=Id[Sets@{o so}]) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition id_to_disc@{o so s | o < so, o < s +} :
  Id[Sets@{o so}] ⟹ PDiscT@{o so s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{o so}])
                     (G:=PDiscT@{o so s}) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition disc_id_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} PDiscMonad@{o so s u u0} (IdMonad@{so o} Sets@{o so}).
Proof.
  unshelve refine {| mh_transform := disc_to_id@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition id_disc_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} (IdMonad@{so o} Sets@{o so}) PDiscMonad@{o so s u u0}.
Proof.
  unshelve refine {| mh_transform := id_to_disc@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Example disc_id_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform disc_id_hom@{o so s u u0}] x = id := eq_refl.

Example id_disc_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform id_disc_hom@{o so s u u0}] x = id := eq_refl.

Definition disc_id_iso@{o so s u u0 m1 m2 |
  o < so, o < s, o < u, so <= m1, o <= m1, so <= m2, o <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
    (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
                     (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
                     (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so}))
                     disc_id_hom@{o so s u u0} id_disc_hom@{o so s u u0}
                     _ _);
    intros x z; simpl; reflexivity.
Defined.

(* * ** The comparison 函子 forgetful 函子 （已译） *)

Definition PDiscK@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
      PDiscMonad@{o so s u u0} :=
  EM_Comparison PDisc_PForget@{o so u u0}.

Example PDiscK_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] X = fobj[PForget@{o so}] X
  := eq_refl.

Example PDiscK_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] f = fmap[PForget@{o so}] f
  := eq_refl.

(* The structure map K X 恒等 setoid 态射 itself. （已译） *)
Example PDiscK_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  t_alg[`2 (fobj[PDiscK@{o so s u u0 e}] X)] = setoid_morphism_id
  := eq_refl.

Definition PDiscK_forget_strict@{o so s u u0 e a b |
  o < so, o < s, o < u, so <= e, o < b, so <= a, o <= a +} :
  @equiv _ (@Functor_StrictEq_Setoid@{a a so so b o} PTopCat@{o so}
              Sets@{o so})
    (EM_Forget _ ◯ PDiscK@{o so s u u0 e}) PForget@{o so}.
Proof.
  exists (fun X => eq_refl).
  intros X Y f. reflexivity.
Defined.

Definition PDiscK_forget@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  EM_Forget _ ◯ PDiscK@{o so s u u0 e} ≈ PForget@{o so} :=
  EM_Comparison_Forget PDisc_PForget@{o so u u0}.

(** ** Set^I = Set *)

Lemma PDiscMonad_alg_id@{o so s u u0 | o < so, o < s, o < u +}
  (a : Sets@{o so})
  (ν : @TAlgebra Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0} a)
  (x : a) : t_alg[ν] x ≈ x.
Proof. exact (@t_id _ _ _ _ ν x). Qed.

Definition EM_PDisc_counit@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0}
    ◯ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
    ≈ Id[Sets@{o so}].
Proof.
  exists (fun x => iso_id).
  intros x y f z; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit_iso@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +}
  (X : @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
         PDiscMonad@{o so s u u0}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    X (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
              PDiscMonad@{o so s u u0}
             ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
                 PDiscMonad@{o so s u u0}] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (PDiscMonad_alg_id _ (`2 X) x).
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (symmetry (PDiscMonad_alg_id _ (`2 X) x)).
  - intro x; simpl. reflexivity.
  - intro x; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Id[@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}]
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
        ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0}.
Proof.
  exists EM_PDisc_unit_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

Definition EM_PDisc_equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}) :=
  @Build_EquivalenceOfCategories _ _ _ _
    EM_PDisc_counit@{o so s u u0 e} EM_PDisc_unit@{o so s u u0 e}.

Definition PDiscK_free_iso@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    (fobj[PDiscK@{o so s u u0 e}] X)
    (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X).
Proof.
  unshelve econstructor;
    [ unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | | ]; intro x; simpl; reflexivity.
Defined.

Definition PDiscK_free@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PDiscK@{o so s u u0 e}
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0} ◯ PForget@{o so}.
Proof.
  exists PDiscK_free_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

(* The comparison 进入 algebras [IdMonad Sets], through θ* the
 态射 单子 [id_disc_hom]. （已译） *)
Definition PDiscKI@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} Id[Sets@{o so}]
      (IdMonad@{so o} Sets@{o so}) :=
  mh_EM@{so o e s} id_disc_hom@{o so s u u0} ◯ PDiscK@{o so s u u0 e}.

Example PDiscKI_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] X
    = fobj[PForget@{o so}] X := eq_refl.

Example PDiscKI_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] f
    = fmap[PForget@{o so}] f := eq_refl.

Example PDiscKI_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) (x : X) :
  t_alg[`2 (fobj[PDiscKI@{o so s u u0 e}] X)] x = x := eq_refl.

(* * ** Not full, not 等价, not monadic （已译） *)

Definition pbool_to_indisc@{o so | o < so +} :
  PBool@{o} ~{PTopCat@{o so}}~> PTwoIndisc@{o} :=
  pindisc_mor _ PBool@{o} setoid_morphism_id.

Lemma no_pindisc_to_bool@{o so | o < so +}
  (g : PTwoIndisc@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  (∀ b : bool, pmap g b = b) → False.
Proof.
  intros Hg.
  assert (Hopen : POpen PTwoIndisc@{o} (fun b => pmap g b = true)).
  { apply (pcont g (fun b => b = true)).
    unfold pdisc_open. intros x y Hxy e. cbn in Hxy. destruct Hxy. exact e. }
  assert (H : pmap g false = true) by exact (Hopen true false (Hg true)).
  rewrite (Hg false) in H. discriminate H.
Qed.

Lemma PForget_not_Full@{o so | o < so +} : Full PForget@{o so} → False.
Proof.
  intros HF.
  apply (no_pindisc_to_bool
           (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id b).
Qed.

(* Every monadic 函子 conservative, [PForget] not: it sends
 [pbool_to_indisc] 同构 [Sets], one.
 Hypothesis 3 Monad/Monadicity/Crude.v's crude monadicity theorem. （已译） *)
Lemma PForget_not_ReflectsIsos@{o so | o < so +} :
  ReflectsIsos PForget@{o so} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{o so} _ _
                 (fmap[PForget@{o so}] pbool_to_indisc@{o so})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_pindisc_to_bool g).
  intro b. exact (Hr b).
Qed.

Lemma PDiscK_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscK@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscK_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscK@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscK_not_Full (Equivalence_Full E)). Qed.

(* The comparison 进入 algebras [IdMonad Sets] not full either:
 恒等 [bool] algebra map KI PTwoIndisc → KI PBool. （已译） *)
Lemma PDiscKI_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscKI@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscKI_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscKI@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscKI_not_Full (Equivalence_Full E)). Qed.

Lemma PDiscK_not_Cat_iso@{o so s u u0 c | o < so, o < s, o < u, so < c +} :
  @IsIsomorphism Cat _ _ PDiscK@{o so s u u0 so} → False.
Proof.
  intros I.
  apply PDiscK_not_Equivalence.
  exact (@Build_EquivalenceOfCategories _ _ _ (@two_sided_inverse _ _ _ _ I)
           (@is_right_inverse _ _ _ _ I)
           (symmetry (@is_left_inverse _ _ _ _ I))).
Qed.

Lemma PForget_not_Monadic@{o so m m0 m1 m3 m6 |
  o < so, o < m0, so <= m, so <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 so m3 o so m6} PForget@{o so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{o so} _ _
                   (fmap[EM_Forget _] (fmap[K] pbool_to_indisc@{o so})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} g b).
  - exact (Hr b).
Qed.
