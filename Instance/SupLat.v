(** * Complete semilattices are the algebras of the power-set monad *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The two-element subset {x, y} *)

(* The subset {x, y} of a setoid, as the union of #227's two truncated
   singletons. *)
Definition Powerset_Prop_pair@{o} {X : SetoidObject@{o o}}
  (x y : carrier X) : carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, Powerset_squash@{o} (@equiv _ (is_setoid X) x z)
             \/ Powerset_squash@{o} (@equiv _ (is_setoid X) y z)) _).
  intros z z' E; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H; intro e; apply k.
  - now transitivity z.
  - now transitivity z.
  - transitivity z'; [exact e | now symmetry].
  - transitivity z'; [exact e | now symmetry].
Defined.

Lemma Powerset_Prop_pair_respects@{o} {X : SetoidObject@{o o}}
  (x x' y y' : carrier X)
  (Ex : @equiv _ (is_setoid X) x x') (Ey : @equiv _ (is_setoid X) y y') :
  Powerset_Prop_pair@{o} x y ≈ Powerset_Prop_pair@{o} x' y'.
Proof.
  intro z; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H; intro e; apply k.
  - transitivity x; [now symmetry | exact e].
  - transitivity y; [now symmetry | exact e].
  - transitivity x'; [exact Ex | exact e].
  - transitivity y'; [exact Ey | exact e].
Qed.

Lemma Powerset_Prop_pair_comm@{o} {X : SetoidObject@{o o}}
  (x y : carrier X) :
  Powerset_Prop_pair@{o} x y ≈ Powerset_Prop_pair@{o} y x.
Proof.
  intro z; split; intros [H|H]; [right|left|right|left]; exact H.
Qed.

(* A singleton {x} lies inside every subset that contains x. *)
Lemma Powerset_Prop_singleton_sub@{o} {X : SetoidObject@{o o}}
  (x : carrier X) (S : carrier (Powerset_Prop_obj@{o} X)) (Hx : S x) :
  ∀ z, Powerset_Prop_singleton_pred@{o} x z → S z.
Proof.
  intros z Hz; apply Hz; intro e.
  exact (proj1 (proper_morphism S x z e) Hx).
Qed.

(* ⋃ {S, T} ≈ T when S ⊆ T. *)
Lemma Powerset_union_pair_sub@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) (HST : ∀ z, S z → T z) :
  Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T) ≈ T.
Proof.
  intro z; split.
  - intros [U [[HU|HU] Hz]]; apply HU; intro e.
    + apply HST. exact (proj2 (e z) Hz).
    + exact (proj2 (e z) Hz).
  - intro Hz. exists T; split; [ right | exact Hz ].
    apply Powerset_squash_intro; reflexivity.
Qed.

(* The family {{x, y} | x ∈ S} ∪ {{y}}, whose union is S ∪ {y}. *)
Definition Powerset_Prop_least_family@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier X) :
  carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X))
       (is_setoid (Powerset_Prop_obj@{o} X))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ U, Powerset_squash@{o}
               (∃ x, S x ∧ @equiv _ (is_setoid (Powerset_Prop_obj@{o} X))
                             (Powerset_Prop_pair@{o} x y) U)
             \/ Powerset_squash@{o}
                  (@equiv _ (is_setoid (Powerset_Prop_obj@{o} X))
                     (Powerset_Prop_singleton_pred@{o} y) U)) _).
  intros U U' E; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H.
  - intros [x [Hx e]]; apply k; exists x; split; [exact Hx | ].
    now transitivity U.
  - intro e; apply k; now transitivity U.
  - intros [x [Hx e]]; apply k; exists x; split; [exact Hx | ].
    transitivity U'; [exact e | now symmetry].
  - intro e; apply k; transitivity U'; [exact e | now symmetry].
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Complete semilattices *)

(* Mac Lane's definition, order first: a partial order in which every
   subset has a supremum.  The order is [Prop]-valued, antisymmetry lands
   in the carrier's ≈, and the supremum is a setoid map out of #227's
   subsets. *)
Record SupLatObject@{o} := {
  sl_set : SetoidObject@{o o};
  sl_le : carrier sl_set → carrier sl_set → Prop;
  sl_le_refl x : sl_le x x;
  sl_le_trans x y z : sl_le x y → sl_le y z → sl_le x z;
  sl_le_respects x x' y y' :
    @equiv _ (is_setoid sl_set) x x' → @equiv _ (is_setoid sl_set) y y' →
    sl_le x y → sl_le x' y';
  sl_antisym x y :
    sl_le x y → sl_le y x → @equiv _ (is_setoid sl_set) x y;
  sl_sup : SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} sl_set) sl_set;
  sl_sup_ub (S : carrier (Powerset_Prop_obj@{o} sl_set)) x :
    S x → sl_le x (sl_sup S);
  sl_sup_least (S : carrier (Powerset_Prop_obj@{o} sl_set)) y :
    (∀ x, S x → sl_le x y) → sl_le (sl_sup S) y
}.

(* A morphism preserves sups; monotonicity is derived below
   ([SupLatHom_monotone]). *)
Record SupLatHom@{o} (A B : SupLatObject@{o}) := {
  slh_map : SetoidMorphism@{o o o} (sl_set A) (sl_set B);
  slh_sup (S : carrier (Powerset_Prop_obj@{o} (sl_set A))) :
    @equiv _ (is_setoid (sl_set B))
      (slh_map (sl_sup A S))
      (sl_sup B (Powerset_Prop_image@{o} slh_map S))
}.

Arguments slh_map {A B} _.
Arguments slh_sup {A B} _ _.

Definition SupLatHom_Setoid@{o} (A B : SupLatObject@{o}) :
  Setoid@{o o} (SupLatHom@{o} A B).
Proof.
  unshelve refine
    (@Build_Setoid@{o o} (SupLatHom@{o} A B)
       (λ f g, @equiv _ (@SetoidMorphism_Setoid@{o o o} (sl_set A) (sl_set B))
                 (slh_map f) (slh_map g)) _).
  constructor.
  - intros f; reflexivity.
  - intros f g H; now symmetry.
  - intros f g h H1 H2; now transitivity (slh_map g).
Defined.

Definition SupLat_id@{o} (A : SupLatObject@{o}) : SupLatHom@{o} A A.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} A A (@setoid_morphism_id@{o o o} (sl_set A)) _).
  intro S. apply (proper_morphism (sl_sup A)).
  symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
Defined.

Definition SupLat_compose@{o} {A B C : SupLatObject@{o}}
  (g : SupLatHom@{o} B C) (f : SupLatHom@{o} A B) : SupLatHom@{o} A C.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} A C
       (@setoid_morphism_compose@{o o o} _ _ _ (slh_map g) (slh_map f)) _).
  intro S. simpl.
  transitivity (slh_map g (sl_sup B (Powerset_Prop_image@{o} (slh_map f) S))).
  { apply proper_morphism. exact (slh_sup f S). }
  transitivity (sl_sup C (Powerset_Prop_image@{o} (slh_map g)
                            (Powerset_Prop_image@{o} (slh_map f) S))).
  { exact (slh_sup g _). }
  apply (proper_morphism (sl_sup C)). symmetry.
  exact (@Powerset_Prop_map_comp@{o} _ _ _ (slh_map g) (slh_map f) S).
Defined.

(* The category of (small) complete semilattices.  It sits at the same
   universes as [Sets@{o so}]. *)
Definition SupLat@{o so} : Category@{so o o}.
Proof.
  unshelve refine
    (@Build_Category@{so o o}
       (SupLatObject@{o} : Type@{so})
       (λ A B, SupLatHom@{o} A B : Type@{o})
       SupLatHom_Setoid@{o} SupLat_id@{o} (@SupLat_compose@{o}) _ _ _ _ _).
  - intros A B C f f' Hf g g' Hg a; simpl.
    transitivity (slh_map f (slh_map g' a)).
    + apply proper_morphism, Hg.
    + apply Hf.
  - intros A B f a; reflexivity.
  - intros A B f a; reflexivity.
  - intros A B C D f g h a; reflexivity.
  - intros A B C D f g h a; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The order recovered from the sup *)

(* x ≤ y exactly when sup {x, y} ≈ y: part (c)'s "in this way". *)
Lemma sl_sup_pair_le@{o} (A : SupLatObject@{o}) (x y : carrier (sl_set A)) :
  iffT@{o o} (sl_le A x y)
    (@equiv _ (is_setoid (sl_set A)) (sl_sup A (Powerset_Prop_pair@{o} x y)) y).
Proof.
  split.
  - intro H. apply sl_antisym.
    + apply sl_sup_least. intros z [Hz|Hz]; apply Hz; intro e.
      * exact (sl_le_respects A x z y y e (reflexivity y) H).
      * exact (sl_le_respects A y z y y e (reflexivity y) (sl_le_refl A y)).
    + apply sl_sup_ub. right. apply Powerset_squash_intro. reflexivity.
  - intro E. apply (sl_le_respects A x x _ y (reflexivity x) E).
    apply sl_sup_ub. left. apply Powerset_squash_intro. reflexivity.
Qed.

(* A sup-preserving map is monotone. *)
Lemma SupLatHom_monotone@{o} {A B : SupLatObject@{o}}
  (f : SupLatHom@{o} A B) (x y : carrier (sl_set A)) :
  sl_le A x y → sl_le B (slh_map f x) (slh_map f y).
Proof.
  intro H.
  destruct (sl_sup_pair_le A x y) as [HA _].
  destruct (sl_sup_pair_le B (slh_map f x) (slh_map f y)) as [_ HB].
  apply HB. pose proof (HA H) as E.
  transitivity (slh_map f (sl_sup A (Powerset_Prop_pair@{o} x y))).
  - symmetry.
    transitivity (sl_sup B (Powerset_Prop_image@{o} (slh_map f)
                              (Powerset_Prop_pair@{o} x y))).
    + exact (slh_sup f _).
    + apply (proper_morphism (sl_sup B)). intro z; split.
      * intro Hz; apply Hz; intros [w [[Hw|Hw] Ew]];
          [left|right]; intros Q k; apply Hw; intro e; apply k;
          (transitivity (slh_map f w);
             [apply proper_morphism; exact e | exact Ew]).
      * intros [Hz|Hz]; apply Hz; intro e; intros Q k; apply k.
        -- exists x; split; [ left | exact e ].
           apply Powerset_squash_intro; reflexivity.
        -- exists y; split; [ right | exact e ].
           apply Powerset_squash_intro; reflexivity.
  - apply proper_morphism. exact E.
Qed.

(* A complete semilattice's carrier has a propositional equality: x ≈ y
   holds exactly when x ≤ y and y ≤ x. *)
Definition sl_PropEquiv@{o} (A : SupLatObject@{o}) :
  PropEquiv@{o o} (is_setoid (sl_set A)).
Proof.
  unshelve refine
    (@Build_PropEquiv@{o o} _ (is_setoid (sl_set A))
       (fun x y => sl_le A x y /\ sl_le A y x) _ _).
  - intros x y [H1 H2]. exact (sl_antisym A x y H1 H2).
  - intros x y E. split.
    + exact (sl_le_respects A x x x y (reflexivity x) E (sl_le_refl A x)).
    + exact (sl_le_respects A x y x x E (reflexivity x) (sl_le_refl A x)).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (c): every complete semilattice is a 𝒫-algebra *)

(* h S := sup S.  Both algebra laws follow by antisymmetry. *)
Definition SupLat_TAlgebra@{o so} (A : SupLatObject@{o}) :
  @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
    (sl_set A).
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
       (sl_set A) (sl_sup A) _ _).
  - intros x. simpl. apply sl_antisym.
    + apply sl_sup_least. intros z Hz. apply Hz; intro E.
      exact (sl_le_respects A x z x x E (reflexivity x) (sl_le_refl A x)).
    + apply sl_sup_ub. apply Powerset_squash_intro; reflexivity.
  - intros SS. simpl. apply sl_antisym.
    + apply sl_sup_least. intros w Hw. apply Hw; intros [S [HS E]].
      apply (sl_le_respects A (sl_sup A S) w _ _ E (reflexivity _)).
      apply sl_sup_least. intros z Hz. apply sl_sup_ub.
      exists S; split; assumption.
    + apply sl_sup_least. intros z [S [HS Hz]].
      apply (sl_le_trans A z (sl_sup A S)).
      * apply sl_sup_ub, Hz.
      * apply sl_sup_ub. apply Powerset_squash_intro.
        exists S; split; [exact HS | reflexivity].
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (b): every 𝒫-algebra is a complete semilattice *)

(* h {x} ≈ x: the algebra's unit law at x. *)
Lemma talg_singleton@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x : carrier X) :
  @equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_singleton_pred@{o} x)) x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* An algebra's carrier has propositional equality: the unit is split mono
   and P X's ≈ is a [Prop] in content. *)
Lemma talg_unsquash@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  Powerset_squash@{o} (@equiv _ (is_setoid X) x y) →
  @equiv _ (is_setoid X) x y.
Proof.
  intro H.
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} x));
    [symmetry; apply talg_singleton|].
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
    [|apply talg_singleton].
  apply proper_morphism. intro z; split; intros Hz Q k; apply H;
    intro exy; apply Hz; intro e; apply k.
  - transitivity x; [now symmetry | exact e].
  - transitivity y; [exact exy | exact e].
Qed.

(* h {h S, h T} ≈ h (S ∪ T): the action law at the pair {S, T}. *)
Lemma talg_pair@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  @equiv _ (is_setoid X)
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S) (t_alg[α] T)))
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T))).
Proof.
  transitivity
    (t_alg[α] (Powerset_Prop_image@{o} t_alg[α] (Powerset_Prop_pair@{o} S T))).
  - apply proper_morphism. intro z; split.
    + intros [H|H]; apply H; intro e; intros Q k; apply k.
      * exists S; split; [ left | exact e ].
        apply Powerset_squash_intro; reflexivity.
      * exists T; split; [ right | exact e ].
        apply Powerset_squash_intro; reflexivity.
    + intro H; apply H; intros [U [[HU|HU] e]]; [left|right];
        intros Q k; apply HU; intro eU; apply k;
        (transitivity (t_alg[α] U);
           [apply proper_morphism; exact eU | exact e]).
  - exact (@t_action _ _ _ _ α (Powerset_Prop_pair@{o} S T)).
Qed.

Lemma talg_mono@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S T : carrier (Powerset_Prop_obj@{o} X)) (HST : ∀ z, S z → T z) :
  @equiv _ (is_setoid X)
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S) (t_alg[α] T)))
    (t_alg[α] T).
Proof.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T))).
  - apply talg_pair.
  - apply proper_morphism. apply Powerset_union_pair_sub, HST.
Qed.

(* Mac Lane's order, x ≤ y iff h {x, y} = y, squashed into [Prop]. *)
Definition talg_le@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) : Prop :=
  Powerset_squash@{o}
    (@equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_pair@{o} x y)) y).

(* The squash is logically inert: [talg_le] IS Mac Lane's condition. *)
Lemma talg_le_iff@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  iffT@{o o} (talg_le@{o so} α x y)
    (@equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_pair@{o} x y)) y).
Proof.
  split.
  - intro H. apply (talg_unsquash α). exact H.
  - intro E. exact (Powerset_squash_intro E).
Qed.

Lemma talg_le_refl@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x : carrier X) : talg_le@{o so} α x x.
Proof.
  apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x)))).
  - apply proper_morphism, Powerset_Prop_pair_respects;
      symmetry; apply talg_singleton.
  - transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} x));
      [|apply talg_singleton].
    apply talg_mono. intros z Hz; exact Hz.
Qed.

Lemma talg_sup_ub@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S : carrier (Powerset_Prop_obj@{o} X)) (x : carrier X) :
  S x → talg_le@{o so} α x (t_alg[α] S).
Proof.
  intro Hx. apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] S))).
  - apply proper_morphism, Powerset_Prop_pair_respects;
      [symmetry; apply talg_singleton | reflexivity].
  - apply talg_mono. apply Powerset_Prop_singleton_sub, Hx.
Qed.

(* Leastness, through the family {{x, y} | x ∈ S} ∪ {{y}}. *)
Lemma talg_sup_least@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier X) :
  (∀ x, S x → talg_le@{o so} α x y) → talg_le@{o so} α (t_alg[α] S) y.
Proof.
  intro Hle. apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S)
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} y)))).
  { apply proper_morphism, Powerset_Prop_pair_respects;
      [reflexivity | symmetry; apply talg_singleton]. }
  rewrite talg_pair.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_least_family@{o} S y))).
  { apply proper_morphism. intro z; split.
    - intros [U [[HU|HU] Hz]]; apply HU; intro e.
      + exists (Powerset_Prop_pair@{o} z y); split.
        * left; apply Powerset_squash_intro; exists z; split;
            [exact (proj2 (e z) Hz) | reflexivity].
        * left; apply Powerset_squash_intro; reflexivity.
      + exists (Powerset_Prop_singleton_pred@{o} y); split.
        * right; apply Powerset_squash_intro; reflexivity.
        * exact (proj2 (e z) Hz).
    - intros [U [[HU|HU] Hz]]; apply HU.
      + intros [x [Hx e]]. destruct (proj2 (e z) Hz) as [Hz'|Hz'].
        * exists S; split; [left; apply Powerset_squash_intro; reflexivity|].
          apply Hz'; intro e'. exact (proj1 (proper_morphism S x z e') Hx).
        * exists (Powerset_Prop_singleton_pred@{o} y); split;
            [right; apply Powerset_squash_intro; reflexivity | exact Hz'].
      + intro e. exists (Powerset_Prop_singleton_pred@{o} y); split;
          [right; apply Powerset_squash_intro; reflexivity
          | exact (proj2 (e z) Hz)]. }
  transitivity
    (t_alg[α] (Powerset_Prop_image@{o} t_alg[α]
                 (Powerset_Prop_least_family@{o} S y))).
  { symmetry.
    exact (@t_action _ _ _ _ α (Powerset_Prop_least_family@{o} S y)). }
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
    [|apply talg_singleton].
  apply proper_morphism. intro w; split.
  - intro Hw; apply Hw; intros [U [[HU|HU] e]]; apply HU.
    + intros [x [Hx eU]]. apply (Hle x Hx); intro Exy.
      intros Q k; apply k.
      transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)); [now symmetry|].
      transitivity (t_alg[α] U); [apply proper_morphism; exact eU | exact e].
    + intro eU. intros Q k; apply k.
      transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
        [symmetry; apply talg_singleton|].
      transitivity (t_alg[α] U); [apply proper_morphism; exact eU | exact e].
  - intro Hw; apply Hw; intro e; intros Q k; apply k.
    exists (Powerset_Prop_singleton_pred@{o} y); split.
    + right; apply Powerset_squash_intro; reflexivity.
    + transitivity y; [apply talg_singleton | exact e].
Qed.

Lemma talg_le_trans@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y z : carrier X) :
  talg_le@{o so} α x y → talg_le@{o so} α y z → talg_le@{o so} α x z.
Proof.
  intros Hxy Hyz. apply Hxy; intro Exy. apply Hyz; intro Eyz.
  apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] (Powerset_Prop_pair@{o} y z)))).
  { apply proper_morphism, Powerset_Prop_pair_respects;
      [symmetry; apply talg_singleton | now symmetry]. }
  rewrite talg_pair.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o}
                 (Powerset_Prop_pair@{o} (Powerset_Prop_pair@{o} x y)
                    (Powerset_Prop_singleton_pred@{o} z)))).
  { apply proper_morphism. intro w; split.
    - intros [U [[HU|HU] Hw]]; apply HU; intro e;
        pose proof (proj2 (e w) Hw) as Hw'.
      + exists (Powerset_Prop_pair@{o} x y); split;
          [left; apply Powerset_squash_intro; reflexivity | left; exact Hw'].
      + destruct Hw' as [Hw'|Hw'].
        * exists (Powerset_Prop_pair@{o} x y); split;
            [left; apply Powerset_squash_intro; reflexivity
            | right; exact Hw'].
        * exists (Powerset_Prop_singleton_pred@{o} z); split;
            [right; apply Powerset_squash_intro; reflexivity | exact Hw'].
    - intros [U [[HU|HU] Hw]]; apply HU; intro e;
        pose proof (proj2 (e w) Hw) as Hw'.
      + destruct Hw' as [Hw'|Hw'].
        * exists (Powerset_Prop_singleton_pred@{o} x); split;
            [left; apply Powerset_squash_intro; reflexivity | exact Hw'].
        * exists (Powerset_Prop_pair@{o} y z); split;
            [right; apply Powerset_squash_intro; reflexivity
            | left; exact Hw'].
      + exists (Powerset_Prop_pair@{o} y z); split;
          [right; apply Powerset_squash_intro; reflexivity
          | right; exact Hw']. }
  rewrite <- talg_pair.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} y z)); [|exact Eyz].
  apply proper_morphism, Powerset_Prop_pair_respects;
    [exact Exy | apply talg_singleton].
Qed.

Lemma talg_le_respects@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x x' y y' : carrier X) :
  @equiv _ (is_setoid X) x x' → @equiv _ (is_setoid X) y y' →
  talg_le@{o so} α x y → talg_le@{o so} α x' y'.
Proof.
  intros Ex Ey H; apply H; intro E; apply Powerset_squash_intro.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)).
  - apply proper_morphism, Powerset_Prop_pair_respects; now symmetry.
  - now transitivity y.
Qed.

Lemma talg_antisym@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  talg_le@{o so} α x y → talg_le@{o so} α y x → @equiv _ (is_setoid X) x y.
Proof.
  intros Hxy Hyx. apply (talg_unsquash α).
  apply Hxy; intro Exy; apply Hyx; intro Eyx; apply Powerset_squash_intro.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} y x)); [now symmetry|].
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)); [|exact Exy].
  apply proper_morphism, Powerset_Prop_pair_comm.
Qed.

(* Part (b): (X, h) as a complete semilattice, with sup S = h S. *)
Definition TAlgebra_SupLat@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  SupLatObject@{o} :=
  @Build_SupLatObject@{o} X (talg_le@{o so} α)
    (talg_le_refl@{o so} α) (talg_le_trans@{o so} α)
    (talg_le_respects@{o so} α) (talg_antisym@{o so} α)
    t_alg[α] (talg_sup_ub@{o so} α) (talg_sup_least@{o so} α).

(* Every 𝒫-algebra's carrier has a propositional equality. *)
Definition talg_PropEquiv@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  PropEquiv@{o o} (is_setoid X).
Proof.
  unshelve refine
    (@Build_PropEquiv@{o o} _ (is_setoid X)
       (fun x y => Powerset_squash@{o} (@equiv _ (is_setoid X) x y)) _ _).
  - intros x y H. exact (talg_unsquash α x y H).
  - intros x y H. exact (Powerset_squash_intro H).
Defined.

(* (b) after (c) gives back the order: "in this way". *)
Lemma sl_talg_le_iff@{o so} (A : SupLatObject@{o})
  (x y : carrier (sl_set A)) :
  iff (talg_le@{o so} (SupLat_TAlgebra@{o so} A) x y) (sl_le A x y).
Proof.
  destruct (sl_sup_pair_le A x y) as [HL HR].
  destruct (talg_le_iff (SupLat_TAlgebra@{o so} A) x y) as [TL TR].
  split.
  - intro H. exact (HR (TL H)).
  - intro H. exact (TR (HL H)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (d): the category of 𝒫-algebras is the category of semilattices *)

Definition EM_to_SupLat@{o so} :
  @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
    Powerset_Monad@{o so} ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       SupLat@{o so}
       (fun x => TAlgebra_SupLat@{o so} (projT2 x))
       (fun x y f =>
          @Build_SupLatHom@{o}
            (TAlgebra_SupLat@{o so} (projT2 x))
            (TAlgebra_SupLat@{o so} (projT2 y))
            (@t_alg_hom _ _ _ _ _ _ _ f)
            (fun S => @t_alg_hom_commutes _ _ _ _ _ _ _ f S))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

Definition SupLat_to_EM@{o so} :
  SupLat@{o so} ⟶
  @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
    Powerset_Monad@{o so}.
Proof.
  unshelve refine
    (@Build_Functor SupLat@{o so}
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       (fun A => existT _ (sl_set A) (SupLat_TAlgebra@{o so} A))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
            Powerset_Monad@{o so} (sl_set A) (sl_set B)
            (SupLat_TAlgebra@{o so} A) (SupLat_TAlgebra@{o so} B)
            (slh_map f) (slh_sup f))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* The algebra round trip, with the identity as its component. *)
Definition SupLat_EM_counit_iso@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so})
    (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so} (projT1 x) (projT1 x)
          (SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} (projT2 x)))
          (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so} (projT1 x) (projT1 x)
          (projT2 x)
          (SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} (projT2 x)))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro S. simpl. apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro S. simpl. apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The semilattice round trip, with the identity as its component. *)
Definition SupLat_EM_unit_iso@{o so} (A : SupLatObject@{o}) :
  @Isomorphism SupLat@{o so}
    (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so}
       (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A
       (@Build_SupLatHom@{o}
          (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A
          (@setoid_morphism_id@{o o o} (sl_set A)) _)
       (@Build_SupLatHom@{o} A
          (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A)
          (@setoid_morphism_id@{o o o} (sl_set A)) _) _ _).
  - intro S. simpl. apply (proper_morphism (sl_sup A)).
    symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro S. simpl. apply (proper_morphism (sl_sup A)).
    symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* Part (d), as an equivalence of categories with identity components. *)
Definition SupLat_EM_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so})
    SupLat_to_EM@{o so}.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ SupLat_to_EM@{o so}
       EM_to_SupLat@{o so} _ _).
  - exists (fun x => SupLat_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (SupLat_EM_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

(* Part (d), as an isomorphism in Cat, built from the two component
   isomorphisms so that both of its natural isomorphisms have the identity
   as every component at [eq_refl]: Theory/Equivalence.v's
   [Equivalence_to_Cat_Iso] would make [iso_from_to] the [symmetry] of the
   unit, which is Theory/Functor.v's opaque [Functor_Setoid_obligation_1]. *)
Definition SupLat_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so}).
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} SupLat@{o so}
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       SupLat_to_EM@{o so} EM_to_SupLat@{o so} _ _).
  - exists (fun x => SupLat_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => SupLat_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* The two legs of the isomorphism are the two functors. *)
Example SupLat_EM_iso_to@{o so c} :
  to SupLat_EM_iso@{o so c} = SupLat_to_EM@{o so} := eq_refl.

Example SupLat_EM_iso_from@{o so c} :
  from SupLat_EM_iso@{o so c} = EM_to_SupLat@{o so} := eq_refl.

(* (b): the carrier is X, sup S = h S as a setoid map, and the order is
   Mac Lane's h {x, y} ≈ y, squashed. *)
Example EM_to_SupLat_carrier@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  sl_set (fobj[EM_to_SupLat@{o so}] x) = projT1 x := eq_refl.

Example EM_to_SupLat_sup@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  sl_sup (fobj[EM_to_SupLat@{o so}] x) = t_alg[projT2 x] := eq_refl.

Example EM_to_SupLat_le@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) (a b : carrier (projT1 x)) :
  sl_le (fobj[EM_to_SupLat@{o so}] x) a b
    = Powerset_squash@{o}
        (@equiv _ (is_setoid (projT1 x))
           (t_alg[projT2 x] (Powerset_Prop_pair@{o} a b)) b) := eq_refl.

(* (c): the carrier is the semilattice's, and h = sup as a setoid map. *)
Example SupLat_to_EM_carrier@{o so} (A : SupLatObject@{o}) :
  projT1 (fobj[SupLat_to_EM@{o so}] A) = sl_set A := eq_refl.

Example SupLat_to_EM_alg@{o so} (A : SupLatObject@{o}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so}] A)] = sl_sup A := eq_refl.

(* The morphisms are carried unchanged. *)
Example EM_to_SupLat_map@{o so}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}) (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so}] f) = t_alg_hom[f] := eq_refl.

Example SupLat_to_EM_map@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  t_alg_hom[fmap[SupLat_to_EM@{o so}] f] = slh_map f := eq_refl.

(* The round trips on data. *)
Example SupLat_EM_rt_carrier@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  projT1 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) = projT1 x
  := eq_refl.

Example SupLat_EM_rt_alg@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x)]
    = t_alg[projT2 x] := eq_refl.

Example SupLat_EM_rt_set@{o so} (A : SupLatObject@{o}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_set A
  := eq_refl.

Example SupLat_EM_rt_sup@{o so} (A : SupLatObject@{o}) :
  sl_sup (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_sup A
  := eq_refl.

Example SupLat_EM_rt_hom@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] f) = slh_map f
  := eq_refl.

Example SupLat_EM_rt_alg_hom@{o so}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}) (f : x ~> y) :
  t_alg_hom[fmap[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] f]
    = t_alg_hom[f] := eq_refl.

(* The components of the equivalence's counit and unit are identities. *)
Example SupLat_EM_counit_component@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           SupLat_EM_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_unit_component@{o so} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (@equivalence_unit _ _ _
                         SupLat_EM_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SupLat_EM_counit_component_from@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             SupLat_EM_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_unit_component_from@{o so} (A : SupLatObject@{o}) :
  slh_map (from (projT1 (@equivalence_unit _ _ _
                           SupLat_EM_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

(* So are those of both natural isomorphisms of the isomorphism in Cat. *)
Example SupLat_EM_iso_to_from_component@{o so c}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[to (projT1 (iso_to_from SupLat_EM_iso@{o so c}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_iso_from_to_component@{o so c} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (iso_from_to SupLat_EM_iso@{o so c}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SupLat_EM_iso_to_from_component_from@{o so c}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[from (projT1 (iso_to_from SupLat_EM_iso@{o so c}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_iso_from_to_component_from@{o so c}
  (A : SupLatObject@{o}) :
  slh_map (from (projT1 (iso_from_to SupLat_EM_iso@{o so c}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.
