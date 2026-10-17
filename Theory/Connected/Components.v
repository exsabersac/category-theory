Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(* * * Connected components: π₀ 范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/connected+component
   nLab:      https://ncatlab.org/nlab/show/full+subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Connected_category
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,

   本文件给出连通分支相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）端、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint zigzag_fmap@{oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) {x y : C}
  (s : ZigZag@{oc hc} x y) : ZigZag@{od hd} (F x) (F y) :=
  match s in ZigZag a b return ZigZag@{od hd} (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (zigzag_fmap F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (zigzag_fmap F s')
  end.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example zigzag_fmap_hom {C D : Category} (F : C ⟶ D) {x y : C} (f : x ~> y) :
  zigzag_fmap F (hom_zigzag f) = hom_zigzag (fmap[F] f) := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zigzag_fmap_id {C : Category} {x y : C} (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s.
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

Lemma zigzag_fmap_compose {C D E : Category} (G : D ⟶ E) (F : C ⟶ D)
  {x y : C} (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s).
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

(* 相关说明。 （已译） *)
Lemma zigzag_fmap_trans {C D : Category} (F : C ⟶ D) {x y z : C}
  (s : ZigZag x y) (t : ZigZag y z) :
  zigzag_fmap F (zigzag_trans s t)
    = zigzag_trans (zigzag_fmap F s) (zigzag_fmap F t).
Proof.
  induction s; simpl; [ reflexivity | f_equal; apply IHs | f_equal; apply IHs ].
Qed.

Lemma zigzag_fmap_sym {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) :
  zigzag_fmap F (zigzag_sym s) = zigzag_sym (zigzag_fmap F s).
Proof.
  induction s; simpl.
  - reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition connected_image@{k oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) (K : Connected@{k oc hc} C)
  (x y : C) : ZigZag@{od hd} (F x) (F y) := zigzag_fmap F (K x y).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition eso_connected@{k l oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D)
  (E : EssentiallySurjective F) (K : Connected@{k oc hc} C) :
  Connected@{l od hd} D :=
  fun d e =>
    zz_bwd (to (eso_iso d))
      (zigzag_trans (connected_image F K (eso_obj d) (eso_obj e))
                    (zz_fwd (to (eso_iso e)) (zz_nil e))).

(* Hence connectedness is invariant under equivalence of categories.  The
   only field of [EquivalenceOfCategories] consumed is its essential
   surjectivity. *)
Definition equivalence_connected {C D : Category} (F : C ⟶ D)
  (E : EquivalenceOfCategories F) (K : Connected C) : Connected D :=
  eso_connected F (Equivalence_EssSurj E) K.

(** ** π₀ as a setoid *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition zigzag_Equivalence (C : Category) : Equivalence (@ZigZag C) :=
  {| Equivalence_Reflexive  := @zz_nil C
   ; Equivalence_Symmetric  := @zigzag_sym C
   ; Equivalence_Transitive := @zigzag_trans C |}.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ObjSetoid@{o h p q} (C : Category@{o h p}) : SetoidObject@{o q} :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence@{o q} obj[C] |} |}.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0 (C : Category) : SetoidObject :=
  SetsQuotient (ObjSetoid C) (@ZigZag C) (zigzag_Equivalence C).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pi0_carrier (C : Category) : carrier (pi0 C) = obj[C] := eq_refl.

Example pi0_equiv (C : Category) (x y : C) :
  @equiv _ (pi0 C) x y = ZigZag x y := eq_refl.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0_coarser@{o h} (C : Category@{o h h}) :
  SetoidCoarser@{o o o o} (A:=ObjSetoid@{o h h o} C) (@ZigZag@{o h} C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0_proj@{o so h} (C : Category@{o h h}) :
  ObjSetoid@{o h h o} C ~{Sets@{o so}}~> pi0@{o o o h} C :=
  sets_quot_proj@{so o} (ObjSetoid@{o h h o} C) (@ZigZag@{o h} C)
    (zigzag_Equivalence@{o o h} C) (pi0_coarser@{o h} C).

(* ... it 恒等 underlying 对象, conversion. （已译） *)
Example pi0_proj_at (C : Category) (x : C) : pi0_proj C x = x := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0_fmap@{o so hc hd} {C : Category@{o hc hc}}
  {D : Category@{o hd hd}} (F : C ⟶ D) :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

(* Its underlying map is the object action of F, by conversion. *)
Example pi0_fmap_at {C D : Category} (F : C ⟶ D) (x : C) :
  pi0_fmap F x = F x := eq_refl.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pi0_fmap_respects {C D : Category} (F G : C ⟶ D) (H : F ≈ G) :
  pi0_fmap F ≈ pi0_fmap G.
Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0_subsingleton (C : Category) : Type :=
  ∀ x y : carrier (pi0 C), x ≈ y.

Definition connected_pi0_subsingleton {C : Category} (K : Connected C) :
  pi0_subsingleton C := K.

Definition pi0_subsingleton_connected {C : Category}
  (H : pi0_subsingleton C) : Connected C := H.

Theorem connected_iff_pi0_subsingleton (C : Category) :
  Connected C ↔ pi0_subsingleton C.
Proof.
  split; [ exact (@connected_pi0_subsingleton C)
         | exact (@pi0_subsingleton_connected C) ].
Defined.

(** ** π₀ as a functor Cat ⟶ Sets *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Pi0 : Cat ⟶ Sets := {|
  fobj := pi0;
  fmap := fun _ _ F => pi0_fmap F
|}.
Next Obligation. intros F G H. exact (pi0_fmap_respects F G H). Defined.
Next Obligation. exact (zz_nil _). Defined.
Next Obligation. exact (zz_nil _). Defined.

Example Pi0_obj (C : Cat) : fobj[Pi0] C = pi0 C := eq_refl.

(* * ** The connected component 对象, full subcategory （已译） *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ComponentSub (C : Category) (x : C) : Subcategory C := {|
  sobj := fun y => ZigZag x y;
  shom := fun _ _ _ _ _ => poly_unit
|}.

Example component_sobj (C : Category) (x y : C) :
  sobj C (ComponentSub C x) y = ZigZag x y := eq_refl.

Definition ConnectedComponent (C : Category) (x : C) : Category :=
  Sub C (ComponentSub C x).

Example component_obj_type (C : Category) (x : C) :
  obj[ConnectedComponent C x] = (∃ y : C, ZigZag x y) := eq_refl.

Definition Component_Incl (C : Category) (x : C) :
  ConnectedComponent C x ⟶ C := Incl C (ComponentSub C x).

Example Component_Incl_obj (C : Category) (x : C)
  (y : ConnectedComponent C x) : Component_Incl C x y = `1 y := eq_refl.

Definition ComponentSub_Full (C : Category) (x : C) :
  Category.Construction.Subcategory.Full C (ComponentSub C x) :=
  fun _ _ _ _ _ => ttt.

Definition Component_Incl_Faithful (C : Category) (x : C) :
  Faithful (Component_Incl C x) := Incl_Faithful C (ComponentSub C x).

Definition Component_Incl_Full (C : Category) (x : C) :
  Functor.Full (Component_Incl C x) :=
  Full_Implies_Full_Functor C (ComponentSub C x) (ComponentSub_Full C x).

(* Every arrow C between two selected 对象 arrow the
 component, selection witness being [ttt]. （已译） *)
Definition component_arr {C : Category} {x : C} {a b : C}
  (sa : ZigZag x a) (sb : ZigZag x b) (f : a ~> b) :
  (a; sa) ~{ConnectedComponent C x}~> (b; sb) := (f; ttt).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition component_iso (C : Category) (x y : C)
  (s t : ZigZag x y) :
  @Isomorphism (ConnectedComponent C x) (y; s) (y; t) := {|
  to := (id[y]; ttt) ; from := (id[y]; ttt)
|}.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint component_lift {C : Category} {x : C} {y z : C}
  (sy : ZigZag x y) (s : ZigZag y z) :
  ∀ sz : ZigZag x z, @ZigZag (ConnectedComponent C x) (y; sy) (z; sz) :=
  match s in ZigZag a b
        return ∀ (sa : ZigZag x a) (sb : ZigZag x b),
               @ZigZag (ConnectedComponent C x) (a; sa) (b; sb) with
  | zz_nil w    => fun sa sb => hom_zigzag (component_arr sa sb (id[w]))
  | zz_fwd f s' => fun sa sb =>
      zz_fwd (component_arr sa (zigzag_trans sa (hom_zigzag f)) f)
             (component_lift (zigzag_trans sa (hom_zigzag f)) s' sb)
  | zz_bwd f s' => fun sa sb =>
      zz_bwd (component_arr (zigzag_trans sa (zz_bwd f (zz_nil _))) sa f)
             (component_lift (zigzag_trans sa (zz_bwd f (zz_nil _))) s' sb)
  end sy.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Component_Connected (C : Category) (x : C) :
  Connected (ConnectedComponent C x).
Proof.
  intros [a sa] [b sb].
  exact (component_lift sa (zigzag_trans (zigzag_sym sa) sb) sb).
Defined.

(* ... and each is inhabited, by its own representative. *)
Definition Component_obj (C : Category) (x : C) : ConnectedComponent C x :=
  (x; zz_nil x).

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Component_Incl_ESO (C : Category) (x : C) (K : Connected C) :
  EssentiallySurjective (Component_Incl C x) :=
  @Build_EssentiallySurjective _ _ (Component_Incl C x)
    (fun d => ((d; K x d) : ConnectedComponent C x)) (fun d => iso_id).

Definition connected_Component_equiv (C : Category) (x : C)
  (K : Connected C) : EquivalenceOfCategories (Component_Incl C x) :=
  @FF_ESO_Equivalence _ _ (Component_Incl C x)
    (Component_Incl_Full C x) (Component_Incl_Faithful C x)
    (Component_Incl_ESO C x K).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition component_reindex_obj {C : Category} {x x' : C} (z : ZigZag x x')
  (y : ConnectedComponent C x) : ConnectedComponent C x' :=
  (`1 y; zigzag_trans (zigzag_sym z) `2 y).

Definition component_reindex_map {C : Category} {x x' : C} (z : ZigZag x x')
  {a b : ConnectedComponent C x} (f : a ~> b) :
  component_reindex_obj z a
    ~{ConnectedComponent C x'}~> component_reindex_obj z b := (`1 f; ttt).

Program Definition Component_reindex {C : Category} {x x' : C}
  (z : ZigZag x x') :
  ConnectedComponent C x ⟶ ConnectedComponent C x' := {|
  fobj := component_reindex_obj z ; fmap := @component_reindex_map C x x' z
|}.

Definition Component_reindex_Faithful (C : Category) (x x' : C)
  (z : ZigZag x x') : Faithful (Component_reindex z).
Proof. construct; simpl in *; auto. Defined.

Definition Component_reindex_Full (C : Category) (x x' : C)
  (z : ZigZag x x') : Functor.Full (Component_reindex z).
Proof.
  construct.
  - exact (`1 g; ttt).
  - simpl; reflexivity.
Defined.

Definition Component_reindex_ESO (C : Category) (x x' : C)
  (z : ZigZag x x') : EssentiallySurjective (Component_reindex z).
Proof.
  unshelve refine (@Build_EssentiallySurjective _ _ _ _ _).
  - intro d; exact ((`1 d; zigzag_trans z `2 d) : ConnectedComponent C x).
  - intros [w s]; simpl.
    exact (component_iso C x' w _ s).
Defined.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Component_reindex_equiv (C : Category) (x x' : C)
  (z : ZigZag x x') :
  EquivalenceOfCategories (Component_reindex z) :=
  @FF_ESO_Equivalence _ _ (Component_reindex z)
    (Component_reindex_Full C x x' z) (Component_reindex_Faithful C x x' z)
    (Component_reindex_ESO C x x' z).

(* 相关说明。 （已译） *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record ConnectedNonempty (C : Category) : Type := {
  cn_obj    : C;
  cn_zigzag : Connected C
}.

Arguments cn_obj {C} _.
Arguments cn_zigzag {C} _.
Arguments Build_ConnectedNonempty {C} _ _.

Definition connected_of_nonempty {C : Category} (K : ConnectedNonempty C) :
  Connected C := cn_zigzag K.

Definition nonempty_connected {C : Category} (c : C) (K : Connected C) :
  ConnectedNonempty C := Build_ConnectedNonempty c K.

(* The empty 范畴 satisfies in-tree reading VACUOUSLY: there no
 pair 对象 join, so function defined zero clauses. （已译） *)
Definition Zero_Connected : Connected _0.
Proof. intros x; destruct x. Defined.

(* ... fails issue's reading, since it has no 对象 at all. （已译） *)
Theorem Zero_not_ConnectedNonempty : ConnectedNonempty _0 → False.
Proof. intro K; destruct (cn_obj K). Qed.

(* 相关说明。 （已译） *)
Definition connected_readings_differ :
  Connected _0 * (ConnectedNonempty _0 → False) :=
  (Zero_Connected, Zero_not_ConnectedNonempty).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Component_ConnectedNonempty (C : Category) (x : C) :
  ConnectedNonempty (ConnectedComponent C x) :=
  Build_ConnectedNonempty (Component_obj C x) (Component_Connected C x).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem connected_nonempty_iff_pi0_singleton (C : Category) :
  ConnectedNonempty C ↔ (carrier (pi0 C) * pi0_subsingleton C).
Proof.
  split.
  - intro K; exact (cn_obj K, cn_zigzag K).
  - intros [c H]; exact (Build_ConnectedNonempty c H).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition terminal_connected {C : Category} (T : @Terminal C) :
  Connected C :=
  fun x y => zz_fwd (@one C T x) (zz_bwd (@one C T y) (zz_nil y)).

Definition is_terminal_connected {C : Category} {c : C}
  (H : IsTerminalObj c) : Connected C :=
  fun x y => zz_fwd (is_terminal_one H (x:=x))
                    (zz_bwd (is_terminal_one H (x:=y)) (zz_nil y)).

Definition terminal_ConnectedNonempty {C : Category} (T : @Terminal C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@terminal_obj C T) (terminal_connected T).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition initial_connected {C : Category} (I : @Initial C) :
  Connected C :=
  fun x y => zz_bwd (@zero C I x) (zz_fwd (@zero C I y) (zz_nil y)).

Definition is_initial_connected {C : Category} {c : C}
  (H : IsInitialObj c) : Connected C :=
  fun x y => zz_bwd (is_initial_zero H (x:=x))
                    (zz_fwd (is_initial_zero H (x:=y)) (zz_nil y)).

Definition initial_ConnectedNonempty {C : Category} (I : @Initial C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@initial_obj C I) (initial_connected I).

(* The point 范畴, directly: single hom one-step chain. （已译） *)
Definition One_Connected : Connected _1 :=
  fun x y => @hom_zigzag _1 x y ttt.

Definition One_ConnectedNonempty : ConnectedNonempty _1 :=
  @Build_ConnectedNonempty _1 ttt One_Connected.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma discrete_zigzag_eq {C : Category} (D : Discrete C) {x y : C}
  (s : ZigZag x y) : x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact `1 (D _ _ f) | exact IH ].
  - transitivity b; [ symmetry; exact `1 (D _ _ f) | exact IH ].
Qed.

Definition discrete_connected_eq {C : Category} (D : Discrete C)
  (K : Connected C) (x y : C) : x = y := discrete_zigzag_eq D (K x y).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem DiscreteCat_connected_iff (A : Type) :
  Connected (DiscreteCat A) ↔ (∀ x y : A, x = y).
Proof.
  split.
  - intros K x y.
    exact (discrete_connected_eq (DiscreteCat_Discrete A) K x y).
  - intros H x y.
    exact (hom_zigzag (H x y : x ~{DiscreteCat A}~> y)).
Defined.

Theorem DiscreteCat_ConnectedNonempty_iff (A : Type) :
  ConnectedNonempty (DiscreteCat A) ↔ (A * (∀ x y : A, x = y)).
Proof.
  split.
  - intro K.
    exact (cn_obj K,
           fun x y => discrete_connected_eq (DiscreteCat_Discrete A)
                        (cn_zigzag K) x y).
  - intros [a H].
    exact (@Build_ConnectedNonempty (DiscreteCat A) a
             (snd (DiscreteCat_connected_iff A) H)).
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem groupoid_connected_iff_arrow {C : Category} (G : IsGroupoid C) :
  Connected C ↔ (∀ x y : C, x ~> y).
Proof.
  split; [ exact (connected_arrow G) | exact (@arrow_connected C) ].
Defined.

(** ** Witnesses *)

(* The walking parallel pair connected: two 对象 joined by
 either two non-恒等 arrows, chain uses one them
 forwards backwards according direction. （已译） *)
Definition Parallel_Connected : Connected Parallel.
Proof.
  intros x y.
  destruct x, y.
  - exact (@zz_nil Parallel ParX).
  - exact (hom_zigzag ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - exact (@zz_bwd Parallel ParY ParX ParX
             ((true; ParOne) : ParX ~{Parallel}~> ParY)
             (@zz_nil Parallel ParX)).
  - exact (@zz_nil Parallel ParY).
Defined.

Definition Parallel_ConnectedNonempty : ConnectedNonempty Parallel :=
  @Build_ConnectedNonempty Parallel ParX Parallel_Connected.

Definition pi0_Parallel_subsingleton : pi0_subsingleton Parallel :=
  Parallel_Connected.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pi0_Roof_subsingleton : pi0_subsingleton Roof := Roof_Connected.

(* The two-element discrete category is NOT connected. *)
Theorem DiscreteCat_bool_not_connected :
  Connected (DiscreteCat bool) → False.
Proof.
  intro K.
  pose proof (fst (DiscreteCat_connected_iff bool) K true false) as H.
  discriminate H.
Qed.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pi0_bool_separates :
  @equiv _ (pi0 (DiscreteCat bool)) true false → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(* 相关说明。 （已译） *)
Theorem component_bool_excludes_false :
  sobj (DiscreteCat bool) (ComponentSub (DiscreteCat bool) true) false
    → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition One_to_bool : _1 ⟶ DiscreteCat bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => eq_refl
|}.

Definition image_connected_not_connected :
  (∀ x y : _1, ZigZag (One_to_bool x) (One_to_bool y))
    * (Connected (DiscreteCat bool) → False) :=
  (connected_image One_to_bool One_Connected, DiscreteCat_bool_not_connected).

(* ... and the hypothesis of [eso_connected] genuinely fails at it: an
   essential-surjectivity witness would supply an isomorphism
   [true ≅ false] in [DiscreteCat bool], whose forward leg is an equality
   of booleans. *)
Theorem One_to_bool_not_ESO :
  EssentiallySurjective One_to_bool → False.
Proof.
  intro E.
  pose proof (to (@eso_iso _ _ One_to_bool E false)) as H.
  discriminate H.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ConnectedDiagram {J C : Category} (D : J ⟶ C) : Type :=
  Connected J.

Definition ConnectedNonemptyDiagram {J C : Category} (D : J ⟶ C) : Type :=
  ConnectedNonempty J.

(* Each IS indexing 范畴's predicate, conversion. Neither a
 tautology: each names new 常值 one side donor
 predicate applied index other. （已译） *)
Example connected_diagram_is_index {J C : Category} (D : J ⟶ C) :
  ConnectedDiagram D = Connected J := eq_refl.

Example connected_nonempty_diagram_is_index {J C : Category} (D : J ⟶ C) :
  ConnectedNonemptyDiagram D = ConnectedNonempty J := eq_refl.

(* 相关说明。 （已译） *)
Definition connected_diagram_of_nonempty {J C : Category} (D : J ⟶ C)
  (K : ConnectedNonemptyDiagram D) : ConnectedDiagram D :=
  connected_of_nonempty K.

(* Connectedness never looks at target: any two diagrams same
 shape connected together not at all. The 证明 恒等,
 honest content remark. （已译） *)
Definition connected_diagram_reindex {J C E : Category}
  (D : J ⟶ C) (D' : J ⟶ E) (K : ConnectedDiagram D) : ConnectedDiagram D'
  := K.

(* 相关说明。 （已译） *)
Definition connected_diagram_pi0 {J C : Category} (D : J ⟶ C)
  (K : ConnectedDiagram D) : pi0_subsingleton J :=
  connected_pi0_subsingleton K.

Definition pi0_connected_diagram {J C : Category} (D : J ⟶ C)
  (H : pi0_subsingleton J) : ConnectedDiagram D :=
  pi0_subsingleton_connected H.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Parallel_ConnectedDiagram {C : Category} (D : Parallel ⟶ C) :
  ConnectedDiagram D := Parallel_Connected.

Definition bool_diagram_not_connected {C : Category}
  (D : DiscreteCat bool ⟶ C) : ConnectedDiagram D → False :=
  DiscreteCat_bool_not_connected.

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
