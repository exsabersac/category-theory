(** * The cylinder C ∏ 2 and the universal natural transformation *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
   Book:      Riehl, "Category Theory in Context" (Dover, 2016), §1.5,
   nLab:      https://ncatlab.org/nlab/show/natural+transformation

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The two inclusions and the universal transformation *)

Program Definition Cyl_incl0 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoX);
  fmap := fun _ _ f => (f, TwoIdX)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

Program Definition Cyl_incl1 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoY);
  fmap := fun _ _ f => (f, TwoIdY)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

(* Restriction along the inclusions: the two ends of a functor on the
   cylinder. *)
Definition Cyl_restrict0 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl0.
Definition Cyl_restrict1 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl1.

(* The universal natural transformation: at each c, the connecting
   arrow of the cylinder. *)
Program Definition Cyl_mu {C : Category} :
  @Cyl_incl0 C ⟹ @Cyl_incl1 C := {|
  transform := fun c => (id[c], TwoXY)
|}.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.

(** ** The classifying functor of a transformation *)

Program Definition Cyl_functor {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : C ∏ _2 ⟶ B := {|
  fobj := fun p => match snd p with
                   | TwoX => S (fst p)
                   | TwoY => T (fst p)
                   end;
  fmap := fun p q fg =>
    match snd fg in TwoHom t t'
      return (match t with TwoX => S (fst p) | TwoY => T (fst p) end
                ~{B}~>
              match t' with TwoX => S (fst q) | TwoY => T (fst q) end)
    with
    | TwoIdX => fmap[S] (fst fg)
    | TwoIdY => fmap[T] (fst fg)
    | TwoXY  => τ (fst q) ∘ fmap[S] (fst fg)
    end
|}.
Next Obligation.
  intros C B S T τ [c t] [c' t'] [f g] [f' g'] [Hf Hg]; simpl in *.
  subst g'.
  destruct g; simpl; now rewrite Hf.
Qed.
Next Obligation.
  intros C B S T τ [c t]; simpl.
  destruct t; simpl; apply fmap_id.
Qed.
Next Obligation.
  (* destruct the walking-arrow OBJECTS first, so _2's composition — a
     match on objects — reduces before the homs are inverted *)
  intros C B S T τ [c t] [c' t'] [c'' t''] [f g] [f' g']; simpl in *.
  destruct t, t', t'';
  try contradiction (TwoHom_Y_X_absurd g);
  try contradiction (TwoHom_Y_X_absurd g');
  pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g;
  pose proof (TwoHom_inv _ _ g') as Hg'; simpl in Hg'; subst g'; simpl.
  - apply fmap_comp.
  - (* crossing after an X-endomorphism *)
    rewrite fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
  - (* Y-endomorphism after the crossing: the naturality square *)
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite <- (naturality[τ]).
    rewrite <- !comp_assoc.
    reflexivity.
  - apply fmap_comp.
Qed.

(** ** The three defining properties *)

(* Restricting the classifying functor to either end recovers the given
   functor, with definitional components. *)
Program Definition Cyl_restrict0_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict0 (Cyl_functor τ) ≈ S :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

Program Definition Cyl_restrict1_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict1 (Cyl_functor τ) ≈ T :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

(* The classifying functor carries the universal transformation to the
   given one. *)
Lemma Cyl_functor_mu {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ c : C, fmap[Cyl_functor τ] (Cyl_mu c) ≈ τ c.
Proof.
  intro c; simpl; cat.
Qed.

(** ** Uniqueness *)

(* Any functor on the cylinder restricting to S and T and carrying μ to
   τ — through the chosen restriction isomorphisms, in the intertwining
   form — is equivalent to the classifying functor. *)
Theorem Cyl_functor_unique {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T)
        (F' : C ∏ _2 ⟶ B)
        (σ0 : Cyl_restrict0 F' ≈ S) (σ1 : Cyl_restrict1 F' ≈ T)
        (Hμ : ∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1 c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0 c))) :
  F' ≈ Cyl_functor τ.
Proof.
  unshelve eexists.
  - intros [c t]; destruct t; simpl.
    + exact (`1 σ0 c).
    + exact (`1 σ1 c).
  - intros [c t] [c' t'] [f g]; simpl.
    destruct t, t';
    try contradiction (TwoHom_Y_X_absurd g);
    pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g; simpl.
    + exact (`2 σ0 c c' f).
    + (* the crossing case: factor (f, TwoXY) ≈ μ c' ∘ (f, TwoIdX) *)
      assert (Hfact : fmap[F'] ((f, TwoXY) : (c, TwoX) ~{C ∏ _2}~> (c', TwoY))
                        ≈ fmap[F'] (Cyl_mu c')
                            ∘ fmap[F'] ((f, TwoIdX) :
                                (c, TwoX) ~{C ∏ _2}~> (c', TwoX))). {
        rewrite <- fmap_comp.
        apply fmap_respects; split; simpl; cat.
      }
      rewrite Hfact.
      (* express F'(μ c') via Hμ and F'(f, TwoIdX) via σ0's naturality *)
      assert (Hmu : fmap[F'] (Cyl_mu c')
                      ≈ from (`1 σ1 c') ∘ (τ c' ∘ to (`1 σ0 c'))). {
        rewrite <- (Hμ c').
        rewrite comp_assoc.
        rewrite iso_from_to, id_left.
        reflexivity.
      }
      rewrite Hmu.
      rewrite (`2 σ0 c c' f); simpl.
      rewrite !comp_assoc.
      rewrite <- (comp_assoc _ (to (`1 σ0 c'))).
      rewrite iso_to_from, id_right.
      reflexivity.
    + exact (`2 σ1 c c' f).
Qed.

(* The universal property, bundled: τ is classified by a functor on the
   cylinder restricting to S and T and carrying μ to τ, uniquely up to
   the ambient functor equivalence. *)
Theorem cylinder_universal {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  { F : C ∏ _2 ⟶ B
  & { σ0 : Cyl_restrict0 F ≈ S
    & { σ1 : Cyl_restrict1 F ≈ T
      & (∀ c, @equiv _ (@homset B (F (c, TwoX)) (T c))
            (to (`1 σ1 c) ∘ fmap[F] (Cyl_mu c))
            (τ c ∘ to (`1 σ0 c)))
        * (∀ F' (σ0' : Cyl_restrict0 F' ≈ S) (σ1' : Cyl_restrict1 F' ≈ T),
             (∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1' c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0' c))) →
             F' ≈ F) } } }.
Proof.
  exists (Cyl_functor τ), (Cyl_restrict0_eq τ), (Cyl_restrict1_eq τ); split.
  - intro c; simpl; cat.
  - intros F' σ0' σ1' Hμ'.
    exact (Cyl_functor_unique τ F' σ0' σ1' Hμ').
Qed.

(** ** The inverse leg: every cylinder functor classifies its own
       transformation *)

(* Reading the transformation off a functor on the cylinder: whisker
   the universal transformation.  Its component at c is
   [fmap[F] (Cyl_mu c)]. *)
Definition Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  Cyl_restrict0 F ⟹ Cyl_restrict1 F :=
  F ⊳ @Cyl_mu C.

(* The round trip: F is the classifier of the transformation it
   carries, through transparent reflexivity witnesses (Construction/
   Arrow/Functor.v's [fs_refl]).  With [cylinder_universal] this
   closes Riehl's bijection in both directions. *)
Theorem Cyl_functor_Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  F ≈ Cyl_functor (Cyl_extract F).
Proof.
  apply (Cyl_functor_unique (Cyl_extract F) F (fs_refl _) (fs_refl _)).
  intro c; simpl; cat.
Qed.
