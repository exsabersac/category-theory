Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Mon.Free.

Generalizable All Variables.

(** * The free commutative monoid on a setoid, and its monad *)

(*
 nLab: https://ncatlab.org/nlab/show/commutative+monoid
 nLab: https://ncatlab.org/nlab/show/multiset
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Finite multisets: lists modulo permutation, letters up to ≈ *)

(* A Prop-valued congruence that stores Type-valued ≈ premises. *)
Inductive perm_eq@{o} {X : SetoidObject@{o o}} : list X → list X → Prop :=
  | pe_nil : perm_eq Datatypes.nil Datatypes.nil
  | pe_skip (a b : X) (l l' : list X) :
      a ≈ b → perm_eq l l' → perm_eq (Datatypes.cons a l) (Datatypes.cons b l')
  | pe_swap (a b : X) (l : list X) :
      perm_eq (Datatypes.cons a (Datatypes.cons b l))
        (Datatypes.cons b (Datatypes.cons a l))
  | pe_transitive (l l' l'' : list X) :
      perm_eq l l' → perm_eq l' l'' → perm_eq l l''.

Lemma perm_eq_refl@{o} {X : SetoidObject@{o o}} (l : list X) : perm_eq l l.
Proof.
  induction l as [|a l IH];
    [ exact pe_nil | exact (pe_skip a a l l (reflexivity a) IH) ].
Qed.

Lemma perm_eq_sym@{o} {X : SetoidObject@{o o}} (l l' : list X) :
  perm_eq l l' → perm_eq l' l.
Proof.
  intro H; induction H as [|a b l l' Hab H IH|a b l|l l' l'' H1 IH1 H2 IH2].
  - exact pe_nil.
  - exact (pe_skip b a l' l (symmetry Hab) IH).
  - exact (pe_swap b a l).
  - exact (pe_transitive _ _ _ IH2 IH1).
Qed.

Definition Bag_Setoid@{o} (X : SetoidObject@{o o}) : Setoid@{o o} (list X) :=
  {| equiv := fun l l' => perm_eq l l'
   ; setoid_equiv := {| Equivalence_Reflexive := @perm_eq_refl X
                      ; Equivalence_Symmetric := @perm_eq_sym X
                      ; Equivalence_Transitive := @pe_transitive X |} |}.

(* The setoid of finite multisets over X. *)
Definition BagObj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier := list X; is_setoid := Bag_Setoid@{o} X |}.

Lemma perm_eq_app_l@{o} {X : SetoidObject@{o o}} (l l' m : list X) :
  perm_eq l l' → perm_eq (wapp l m) (wapp l' m).
Proof.
  intro H; induction H as [|a b l l' Hab H IH|a b l|l l' l'' H1 IH1 H2 IH2];
    simpl.
  - apply perm_eq_refl.
  - exact (pe_skip _ _ _ _ Hab IH).
  - apply pe_swap.
  - exact (pe_transitive _ _ _ IH1 IH2).
Qed.

Lemma perm_eq_app_r@{o} {X : SetoidObject@{o o}} (l m m' : list X) :
  perm_eq m m' → perm_eq (wapp l m) (wapp l m').
Proof.
  intro H; induction l as [|a l IH]; simpl; [ exact H | ].
  exact (pe_skip a a _ _ (reflexivity a) IH).
Qed.

Lemma perm_eq_middle@{o} {X : SetoidObject@{o o}} (a : X) (l m : list X) :
  perm_eq (Datatypes.cons a (wapp l m)) (wapp l (Datatypes.cons a m)).
Proof.
  induction l as [|b l IH]; simpl; [ apply perm_eq_refl | ].
  eapply pe_transitive; [ apply pe_swap | ].
  exact (pe_skip b b _ _ (reflexivity b) IH).
Qed.

Lemma perm_eq_app_comm@{o} {X : SetoidObject@{o o}} (l m : list X) :
  perm_eq (wapp l m) (wapp m l).
Proof.
  induction l as [|a l IH]; simpl.
  - rewrite wapp_nil_r. apply perm_eq_refl.
  - eapply pe_transitive; [ exact (pe_skip a a _ _ (reflexivity a) IH) | ].
    apply perm_eq_middle.
Qed.

(* Mapping the letters respects permutations. *)
Lemma perm_eq_wmap@{o} {X Y : SetoidObject@{o o}} (f : X → Y)
  (fp : Proper (equiv ==> equiv) f) (l l' : list X) :
  perm_eq l l' → perm_eq (wmap f l) (wmap f l').
Proof.
  intro H; induction H as [|a b l l' Hab H IH|a b l|l l' l'' H1 IH1 H2 IH2];
    simpl.
  - exact pe_nil.
  - exact (pe_skip _ _ _ _ (fp a b Hab) IH).
  - apply pe_swap.
  - exact (pe_transitive _ _ _ IH1 IH2).
Qed.

(* Leibniz: mapping commutes with concatenation, and the identity map is
   the identity. *)
Lemma wmap_wapp@{o} {X Y : SetoidObject@{o o}} (f : X → Y) (l m : list X) :
  wmap f (wapp l m) = wapp (wmap f l) (wmap f m).
Proof. induction l as [|a l IH]; simpl; [ reflexivity | now rewrite IH ]. Qed.

Lemma wmap_id@{o} {X : SetoidObject@{o o}} (l : list X) :
  wmap (X := X) (Y := X) (fun x => x) l = l.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | now rewrite IH ]. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The free commutative monoid, its adjunction and its monad *)

Section FreeCMon.

Universes o so.

Local Notation CMonOS := CMon@{so o}.
Local Notation UCMon := (CMon_Forget : CMon@{so o} ⟶ Sets@{o so}).

(* The multisets over X under concatenation; ≈ is the Prop congruence
   [perm_eq] itself, so the PropEquiv field is free. *)
Definition FreeCMonObject@{+} (X : obj[Sets@{o so}]) : CMonOS.
Proof.
  unshelve refine
    {| cmon_setoid := BagObj X
     ; cmon_zero := Datatypes.nil
     ; cmon_plus := @wapp X |}.
  - intros l l' H m m' K.
    exact (pe_transitive _ _ _ (perm_eq_app_l _ _ m H)
             (perm_eq_app_r l' _ _ K)).
  - intros a b c. simpl. rewrite wapp_assoc. apply perm_eq_refl.
  - intros a b. exact (perm_eq_app_comm a b).
  - intros a. apply perm_eq_refl.
  - exact (@PropEquiv_of_relation (list X) (Bag_Setoid X)
             (fun l l' => @perm_eq X l l') (fun _ _ h => h) (fun _ _ h => h)).
Defined.

Example FreeCMon_carrier@{+} (X : obj[Sets@{o so}]) :
  cmon_setoid (FreeCMonObject X) = BagObj X := eq_refl.

Example FreeCMon_plus@{+} (X : obj[Sets@{o so}]) (l m : list X) :
  cmon_plus (FreeCMonObject X) l m = wapp l m := eq_refl.

Example FreeCMon_zero@{+} (X : obj[Sets@{o so}]) :
  cmon_zero (FreeCMonObject X) = @Datatypes.nil X := eq_refl.

(* The insertion of one-letter multisets. *)
Definition bag_insert@{+} (X : obj[Sets@{o so}]) :
  X ~{Sets@{o so}}~> fobj[UCMon] (FreeCMonObject X).
Proof.
  refine {| morphism := fun a => Datatypes.cons a Datatypes.nil |}.
  intros a b H. exact (pe_skip a b _ _ H pe_nil).
Defined.

(* The extension of h along the insertion: the sum h(x1) + ⋯ + h(xn). *)
Fixpoint cfold@{+} {X : obj[Sets@{o so}]} {L : CMonOS} (h : X → L)
  (l : list X) : L :=
  match l with
  | Datatypes.nil => cmon_zero L
  | Datatypes.cons a l' => cmon_plus L (h a) (cfold h l')
  end.

(* The Prop congruence is eliminated into the Prop mirror of L's ≈. *)
Lemma cfold_respects@{+} {X : obj[Sets@{o so}]} {L : CMonOS} (h : X → L)
  (hp : Proper (equiv ==> equiv) h) (l l' : list X) :
  perm_eq l l' → cfold h l ≈ cfold h l'.
Proof.
  intro H. apply (@pequiv_to _ _ (cmon_prop L)).
  induction H as [|a b l l' Hab H IH|a b l|l l' l'' H1 IH1 H2 IH2]; simpl;
    apply pequiv_from.
  - reflexivity.
  - apply cmon_plus_respects; [ exact (hp a b Hab) | exact (pequiv_to _ _ IH) ].
  - rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ apply cmon_plus_comm | reflexivity ].
  - transitivity (cfold h l');
      [ exact (pequiv_to _ _ IH1) | exact (pequiv_to _ _ IH2) ].
Qed.

Lemma cfold_app@{+} {X : obj[Sets@{o so}]} {L : CMonOS} (h : X → L)
  (l m : list X) :
  cfold h (wapp l m) ≈ cmon_plus L (cfold h l) (cfold h m).
Proof.
  induction l as [|a l IH]; simpl.
  - symmetry. apply cmon_plus_zero_l.
  - rewrite IH. symmetry. apply cmon_plus_assoc.
Qed.

Definition cfold_hom@{+} {X : obj[Sets@{o so}]} {L : CMonOS}
  (h : X ~{Sets@{o so}}~> fobj[UCMon] L) : CMonHom (FreeCMonObject X) L.
Proof.
  unshelve refine
    (@Build_CMonHom (FreeCMonObject X) L
       (@Build_SetoidMorphism _ (is_setoid (cmon_setoid (FreeCMonObject X)))
          _ (is_setoid (cmon_setoid L)) (cfold h) _) _ _).
  - intros l l' H. exact (cfold_respects h (proper_morphism h) l l' H).
  - reflexivity.
  - intros l m. exact (cfold_app h l m).
Defined.

(* A homomorphism out of the free commutative monoid is the fold of its
   values on the letters. *)
Lemma cfold_unique@{+} {X : obj[Sets@{o so}]} {L : CMonOS}
  (g : CMonHom (FreeCMonObject X) L) (l : list X) :
  g l ≈ cfold (fun a => g (Datatypes.cons a Datatypes.nil)) l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (cmon_map_zero g).
  - rewrite <- IH.
    exact (cmon_map_plus g (Datatypes.cons a Datatypes.nil) l).
Qed.

Definition FreeCMon_map@{+} {X Y : obj[Sets@{o so}]}
  (f : X ~{Sets@{o so}}~> Y) :
  CMonHom (FreeCMonObject X) (FreeCMonObject Y).
Proof.
  unshelve refine
    (@Build_CMonHom (FreeCMonObject X) (FreeCMonObject Y)
       (@Build_SetoidMorphism _ (is_setoid (cmon_setoid (FreeCMonObject X)))
          _ (is_setoid (cmon_setoid (FreeCMonObject Y))) (wmap f) _) _ _).
  - intros l l' H. exact (perm_eq_wmap f (proper_morphism f) l l' H).
  - simpl. exact pe_nil.
  - intros l m. simpl. rewrite wmap_wapp. apply perm_eq_refl.
Defined.

(* The free functor; on arrows it maps the letters. *)
Definition FreeCMon@{+} : Sets@{o so} ⟶ CMonOS.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} CMonOS FreeCMonObject
       (fun X Y f => FreeCMon_map f) _ _ _).
  - intros X Y f g H l. simpl.
    induction l as [|a l IH]; simpl;
      [ exact pe_nil | exact (pe_skip _ _ _ _ (H a) IH) ].
  - intros X l. simpl.
    induction l as [|a l IH]; simpl;
      [ exact pe_nil | exact (pe_skip _ _ _ _ (reflexivity a) IH) ].
  - intros X Y Z f g l. simpl.
    induction l as [|a l IH]; simpl;
      [ exact pe_nil | exact (pe_skip _ _ _ _ (reflexivity _) IH) ].
Defined.

(* The natural bijection CMon(F X, L) ≅ Sets(X, U L). *)
Definition FreeCMon_adj_iso@{+} (X : obj[Sets@{o so}]) (L : CMonOS) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom CMonOS (FreeCMon X) L
     ; is_setoid := @homset CMonOS (FreeCMon X) L |}
    {| carrier := @hom Sets@{o so} X (UCMon L)
     ; is_setoid := @homset Sets@{o so} X (UCMon L) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       {| carrier := @hom CMonOS (FreeCMon X) L
        ; is_setoid := @homset CMonOS (FreeCMon X) L |}
       {| carrier := @hom Sets@{o so} X (UCMon L)
        ; is_setoid := @homset Sets@{o so} X (UCMon L) |}
       (@Build_SetoidMorphism
          (@hom CMonOS (FreeCMon X) L) (@homset CMonOS (FreeCMon X) L)
          (@hom Sets@{o so} X (UCMon L)) (@homset Sets@{o so} X (UCMon L))
          (fun g => fmap[UCMon] g ∘ bag_insert X) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (UCMon L)) (@homset Sets@{o so} X (UCMon L))
          (@hom CMonOS (FreeCMon X) L) (@homset CMonOS (FreeCMon X) L)
          (fun h => cfold_hom h) _) _ _).
  - intros g g' H a. exact (H _).
  - intros h h' H l. simpl.
    induction l as [|a l IH]; simpl; [ reflexivity | ].
    apply cmon_plus_respects; [ exact (H a) | exact IH ].
  - intros h a. simpl. apply cmon_plus_zero_r.
  - intros g l. simpl. symmetry. exact (cfold_unique g l).
Defined.

(* FreeCMon ⊣ CMon_Forget, in hom-set form, so that the counit computes. *)
Definition FreeCMon_adj@{+} :
  @Adjunction@{so o o so o o o o so o so} CMonOS Sets@{o so} FreeCMon UCMon.
Proof.
  unshelve refine
    (@Build_Adjunction' CMonOS Sets@{o so} FreeCMon UCMon
       FreeCMon_adj_iso _ _).
  - intros X Y L f g a. reflexivity.
  - intros X L L' f g a. reflexivity.
Defined.

(* The free commutative monoid monad: finite multisets. *)
Definition BagF@{+} : Sets@{o so} ⟶ Sets@{o so} := UCMon ◯ FreeCMon.

Definition BagMonad@{+} : @Monad Sets@{o so} BagF :=
  Adjunction_Induced_Monad FreeCMon_adj.

(* μ_X: the union of a multiset of multisets. *)
Definition bconcat@{+} {X : obj[Sets@{o so}]} (ll : list (list X)) : list X :=
  cfold (L := FreeCMonObject X) (fun l => l) ll.

Example Bag_obj@{+} (X : obj[Sets@{o so}]) : fobj[BagF] X = BagObj X
  := eq_refl.

Example Bag_map@{+} {X Y : obj[Sets@{o so}]} (f : X ~{Sets@{o so}}~> Y)
  (l : list X) : fmap[BagF] f l = wmap f l := eq_refl.

Example Bag_ret@{+} (X : obj[Sets@{o so}]) :
  @ret _ _ BagMonad X = bag_insert X := eq_refl.

Example Bag_join_counit@{+} (X : obj[Sets@{o so}]) :
  @join _ _ BagMonad X
    = fmap[UCMon] (@counit _ _ _ _ FreeCMon_adj (FreeCMon X)) := eq_refl.

Example Bag_join@{+} (X : obj[Sets@{o so}]) (ll : list (list X)) :
  @join _ _ BagMonad X ll = bconcat ll := eq_refl.

(* The Eilenberg–Moore category of the multiset monad. *)
Definition BagAlg@{+} : Category@{so o o} :=
  @EilenbergMoore@{so so so o} Sets@{o so} BagF BagMonad.

(* ------------------------------------------------------------------------ *)
(** ** Every algebra is a commutative monoid, on a set *)

Lemma balg_unit@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (a : S) :
  t_alg[α] (Datatypes.cons a Datatypes.nil) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law, on lists of lists: h (map h ll) ≈ h (union ll). *)
Lemma balg_action@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (ll : list (list S)) :
  t_alg[α] (wmap (t_alg[α]) ll) ≈ t_alg[α] (bconcat ll).
Proof. exact (@t_action _ _ _ _ α ll). Qed.

(* a + b = α⟨a b⟩ and 0 = α⟨⟩. *)
Definition balg_plus@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (a b : S) : S :=
  t_alg[α] (Datatypes.cons a (Datatypes.cons b Datatypes.nil)).

Definition balg_zero@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) : S :=
  t_alg[α] Datatypes.nil.

Lemma balg_resp@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) :
  Proper (equiv ==> equiv ==> equiv) (balg_plus α).
Proof.
  intros a a' Ha b b' Hb. apply (proper_morphism (t_alg[α])).
  exact (pe_skip _ _ _ _ Ha (pe_skip _ _ _ _ Hb pe_nil)).
Qed.

(* Commutativity is one swap. *)
Lemma balg_comm@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (a b : S) :
  balg_plus α a b ≈ balg_plus α b a.
Proof.
  apply (proper_morphism (t_alg[α])). exact (pe_swap a b Datatypes.nil).
Qed.

Lemma balg_assoc@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (a b c : S) :
  balg_plus α (balg_plus α a b) c ≈ balg_plus α a (balg_plus α b c).
Proof.
  unfold balg_plus.
  set (w1 := fun x : S => Datatypes.cons x Datatypes.nil).
  set (w2 := fun x y : S => Datatypes.cons x (Datatypes.cons y Datatypes.nil)).
  transitivity (t_alg[α] (w2 (t_alg[α] (w2 a b)) (t_alg[α] (w1 c)))).
  { apply (proper_morphism (t_alg[α])).
    exact (pe_skip _ _ _ _ (reflexivity _)
             (pe_skip _ _ _ _ (symmetry (balg_unit α c)) pe_nil)). }
  transitivity (t_alg[α] (bconcat (Datatypes.cons (w2 a b)
                                     (Datatypes.cons (w1 c) Datatypes.nil)))).
  { exact (balg_action α (Datatypes.cons (w2 a b)
                            (Datatypes.cons (w1 c) Datatypes.nil))). }
  transitivity (t_alg[α] (bconcat (Datatypes.cons (w1 a)
                                     (Datatypes.cons (w2 b c) Datatypes.nil)))).
  { reflexivity. }
  transitivity (t_alg[α] (w2 (t_alg[α] (w1 a)) (t_alg[α] (w2 b c)))).
  { symmetry.
    exact (balg_action α (Datatypes.cons (w1 a)
                            (Datatypes.cons (w2 b c) Datatypes.nil))). }
  apply (proper_morphism (t_alg[α])).
  exact (pe_skip _ _ _ _ (balg_unit α a)
           (pe_skip _ _ _ _ (reflexivity _) pe_nil)).
Qed.

Lemma balg_zero_l@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (a : S) :
  balg_plus α (balg_zero α) a ≈ a.
Proof.
  unfold balg_plus, balg_zero.
  transitivity
    (t_alg[α] (Datatypes.cons (t_alg[α] Datatypes.nil)
                 (Datatypes.cons (t_alg[α] (Datatypes.cons a Datatypes.nil))
                    Datatypes.nil))).
  { apply (proper_morphism (t_alg[α])).
    exact (pe_skip _ _ _ _ (reflexivity _)
             (pe_skip _ _ _ _ (symmetry (balg_unit α a)) pe_nil)). }
  transitivity
    (t_alg[α] (bconcat (Datatypes.cons Datatypes.nil
                          (Datatypes.cons (Datatypes.cons a Datatypes.nil)
                             Datatypes.nil)))).
  { exact (balg_action α (Datatypes.cons Datatypes.nil
                            (Datatypes.cons (Datatypes.cons a Datatypes.nil)
                               Datatypes.nil))). }
  exact (balg_unit α a).
Qed.

(* The carrier of every algebra is a SET: x ≈ y iff ⟨x⟩ and ⟨y⟩ are equal
   multisets, so EM_to_CMon needs no hypothesis. *)
Definition balg_prop@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) : PropEquiv (is_setoid S).
Proof.
  unshelve refine
    {| pequiv := fun x y : S =>
         perm_eq (Datatypes.cons x Datatypes.nil)
           (Datatypes.cons y Datatypes.nil) |}.
  - intros x y H.
    transitivity (t_alg[α] (Datatypes.cons x Datatypes.nil));
      [ symmetry; exact (balg_unit α x) | ].
    transitivity (t_alg[α] (Datatypes.cons y Datatypes.nil));
      [ exact (proper_morphism (t_alg[α]) _ _ H) | exact (balg_unit α y) ].
  - intros x y H. exact (pe_skip _ _ _ _ H pe_nil).
Defined.

(* The commutative monoid of an algebra. *)
Definition balg_cmon@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) : CMonOS :=
  {| cmon_setoid := S
   ; cmon_zero := balg_zero α
   ; cmon_plus := balg_plus α
   ; cmon_plus_respects := balg_resp α
   ; cmon_plus_assoc := balg_assoc α
   ; cmon_plus_comm := balg_comm α
   ; cmon_plus_zero_l := balg_zero_l α
   ; cmon_prop := balg_prop α |}.

(* The algebra comes from its commutative monoid: α⟨m1 … mn⟩ ≈ m1 + ⋯ + mn. *)
Lemma balg_fold@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} BagF BagMonad S) (l : list S) :
  cfold (L := balg_cmon α) (fun x => x) l ≈ t_alg[α] l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  change (balg_plus α a (cfold (L := balg_cmon α) (fun x => x) l)
            ≈ t_alg[α] (Datatypes.cons a l)).
  unfold balg_plus.
  transitivity
    (t_alg[α] (Datatypes.cons (t_alg[α] (Datatypes.cons a Datatypes.nil))
                 (Datatypes.cons (t_alg[α] l) Datatypes.nil))).
  { apply (proper_morphism (t_alg[α])).
    exact (pe_skip _ _ _ _ (symmetry (balg_unit α a))
             (pe_skip _ _ _ _ IH pe_nil)). }
  transitivity
    (t_alg[α] (bconcat (Datatypes.cons (Datatypes.cons a Datatypes.nil)
                          (Datatypes.cons l Datatypes.nil)))).
  { exact (balg_action α (Datatypes.cons (Datatypes.cons a Datatypes.nil)
                            (Datatypes.cons l Datatypes.nil))). }
  apply (proper_morphism (t_alg[α])).
  change (perm_eq (Datatypes.cons a (wapp l Datatypes.nil))
            (Datatypes.cons a l)).
  rewrite wapp_nil_r. apply perm_eq_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The Eilenberg–Moore category of the multiset monad is CMon *)

Definition EM_cmon_map@{+} {x y : BagAlg} (f : x ~{BagAlg}~> y) :
  CMonHom (balg_cmon (projT2 x)) (balg_cmon (projT2 y)).
Proof.
  unshelve refine
    (@Build_CMonHom (balg_cmon (projT2 x)) (balg_cmon (projT2 y))
       (t_alg_hom[f]) _ _).
  - exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f Datatypes.nil).
  - intros a b.
    exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f
             (Datatypes.cons a (Datatypes.cons b Datatypes.nil))).
Defined.

Definition EM_to_CMon@{+} : BagAlg ⟶ CMonOS.
Proof.
  unshelve refine
    (@Build_Functor BagAlg CMonOS (fun x => balg_cmon (projT2 x))
       (fun x y f => EM_cmon_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : CMon → Set^Bag. *)
Definition CMon_K@{+} : CMonOS ⟶ BagAlg := EM_Comparison FreeCMon_adj.

Definition CMon_EM_counit_iso@{+} (x : BagAlg) :
  @Isomorphism BagAlg (fobj[CMon_K ◯ EM_to_CMon] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism BagAlg (fobj[CMon_K ◯ EM_to_CMon] x) x
       (@Build_TAlgebraHom Sets@{o so} BagF BagMonad (projT1 x) (projT1 x)
          (projT2 (fobj[CMon_K ◯ EM_to_CMon] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} BagF BagMonad (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[CMon_K ◯ EM_to_CMon] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro l. simpl. rewrite wmap_id. exact (balg_fold (projT2 x) l).
  - intro l. simpl. rewrite wmap_id. symmetry. exact (balg_fold (projT2 x) l).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The commutative monoid round trip: the sum comes back as a + (b + 0). *)
Definition CMon_EM_unit_iso@{+} (M : CMonOS) :
  @Isomorphism CMonOS (fobj[EM_to_CMon ◯ CMon_K] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism CMonOS (fobj[EM_to_CMon ◯ CMon_K] M) M
       (@Build_CMonHom (fobj[EM_to_CMon ◯ CMon_K] M) M
          (@setoid_morphism_id@{o o o} (cmon_setoid M)) _ _)
       (@Build_CMonHom M (fobj[EM_to_CMon ◯ CMon_K] M)
          (@setoid_morphism_id@{o o o} (cmon_setoid M)) _ _) _ _).
  - reflexivity.
  - intros a b. simpl.
    apply cmon_plus_respects; [ reflexivity | apply cmon_plus_zero_r ].
  - reflexivity.
  - intros a b. simpl. symmetry.
    apply cmon_plus_respects; [ reflexivity | apply cmon_plus_zero_r ].
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

Definition CMon_EM_equivalence@{+} :
  @EquivalenceOfCategories@{so so so so so o} CMonOS BagAlg CMon_K.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ CMon_K EM_to_CMon _ _).
  - exists (fun x => CMon_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => iso_sym (CMon_EM_unit_iso M)).
    intros M N f a. reflexivity.
Defined.

(* Commutative monoids are monadic over Set. *)
Definition CMon_Forget_Monadic@{+} :
  @Monadic@{so so so so so o so so} CMonOS Sets@{o so} UCMon.
Proof.
  exists FreeCMon. exists FreeCMon_adj. exact CMon_EM_equivalence.
Defined.

(* CMon ≅ Set^Bag in Cat, from the two component isomorphisms. *)
Definition CMon_EM_iso@{c +} : @Isomorphism Cat@{c so so so o} CMonOS BagAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} CMonOS BagAlg CMon_K EM_to_CMon
       _ _).
  - exists (fun x => CMon_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => CMon_EM_unit_iso M). intros M N f a. reflexivity.
Defined.

(* Commuting with the forgetful functors. *)
Theorem CMon_K_Forget@{+} :
  @EM_Forget Sets@{o so} BagF BagMonad ◯ CMon_K ≈ UCMon.
Proof. exact (EM_Comparison_Forget FreeCMon_adj). Qed.

Theorem EM_to_CMon_Forget@{+} :
  UCMon ◯ EM_to_CMon ≈ @EM_Forget Sets@{o so} BagF BagMonad.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

Example CMon_EM_iso_to@{+} : to CMon_EM_iso = CMon_K := eq_refl.

Example CMon_EM_iso_from@{+} : from CMon_EM_iso = EM_to_CMon := eq_refl.

(* K M = ⟨M, U ε_M⟩, the structure map the fold of the identity. *)
Example CMon_K_alg_fun@{+} (M : CMonOS) (l : list (cmon_setoid M)) :
  t_alg[projT2 (fobj[CMon_K] M)] l = cfold (L := M) (fun x => x) l
  := eq_refl.

Example CMon_K_zero@{+} (M : CMonOS) :
  t_alg[projT2 (fobj[CMon_K] M)] Datatypes.nil = cmon_zero M := eq_refl.

Example CMon_K_map@{+} {M N : CMonOS} (f : M ~{CMonOS}~> N) :
  t_alg_hom[fmap[CMon_K] f] = cmon_map f := eq_refl.

(* The commutative monoid of an algebra: a + b = α⟨a b⟩, 0 = α⟨⟩. *)
Example EM_to_CMon_plus@{+} (x : BagAlg) (a b : projT1 x) :
  cmon_plus (fobj[EM_to_CMon] x) a b
    = t_alg[projT2 x] (Datatypes.cons a (Datatypes.cons b Datatypes.nil))
  := eq_refl.

Example EM_to_CMon_zero@{+} (x : BagAlg) :
  cmon_zero (fobj[EM_to_CMon] x) = t_alg[projT2 x] Datatypes.nil := eq_refl.

Example CMon_rt_carrier@{+} (M : CMonOS) :
  cmon_setoid (fobj[EM_to_CMon ◯ CMon_K] M) = cmon_setoid M := eq_refl.

Example CMon_rt_zero@{+} (M : CMonOS) :
  cmon_zero (fobj[EM_to_CMon ◯ CMon_K] M) = cmon_zero M := eq_refl.

Example CMon_rt_plus_fun@{+} (M : CMonOS) (a b : cmon_setoid M) :
  cmon_plus (fobj[EM_to_CMon ◯ CMon_K] M) a b
    = cmon_plus M a (cmon_plus M b (cmon_zero M)) := eq_refl.

Example CMon_rt_hom@{+} {M N : CMonOS} (f : M ~{CMonOS}~> N) :
  cmon_map (fmap[EM_to_CMon ◯ CMon_K] f) = cmon_map f := eq_refl.

Example EM_CMon_rt_carrier@{+} (x : BagAlg) :
  projT1 (fobj[CMon_K ◯ EM_to_CMon] x) = projT1 x := eq_refl.

Example EM_CMon_rt_alg_hom@{+} {x y : BagAlg} (f : x ~{BagAlg}~> y) :
  t_alg_hom[fmap[CMon_K ◯ EM_to_CMon] f] = t_alg_hom[f] := eq_refl.

Example CMon_EM_iso_to_from_component@{+} (x : BagAlg) :
  (t_alg_hom[to (projT1 (iso_to_from CMon_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from CMon_EM_iso) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example CMon_EM_iso_from_to_component@{+} (M : CMonOS) :
  (cmon_map (to (projT1 (iso_from_to CMon_EM_iso) M)),
   cmon_map (from (projT1 (iso_from_to CMon_EM_iso) M)))
    = (@setoid_morphism_id@{o o o} (cmon_setoid M),
       @setoid_morphism_id@{o o o} (cmon_setoid M)) := eq_refl.

(* The Prop mirror of an algebra's carrier: ⟨x⟩ and ⟨y⟩ as multisets. *)
Example balg_prop_is@{+} (x : BagAlg) (a b : projT1 x) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_CMon] x)) a b
    = perm_eq (Datatypes.cons a Datatypes.nil)
        (Datatypes.cons b Datatypes.nil) := eq_refl.

End FreeCMon.
