Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * [Sets] is complete *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Complete_category

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Section SetsLimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* The compatibility constraint cutting the limit out of the indexed product
   of the [F d]: a family is compatible when its components agree along every
   arrow of [D]. *)
Definition Sets_limit_compatible (x : Sets_iprod_obj (fun d : D => F d)) :
  Type :=
  ∀ (d d' : D) (f : d ~{D}~> d'), fmap[F] f (x d) ≈ x d'.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_limit_carrier : Type :=
  { x : Sets_iprod_obj (fun d : D => F d) & Sets_limit_compatible x }.

(* Two compatible families are identified when the underlying families are:
   the constraint witness plays no part, exactly as in Instance/Sets/End.v. *)
Definition Sets_limit_equiv : crelation Sets_limit_carrier :=
  fun p q => `1 p ≈ `1 q.

Program Definition Sets_limit_obj : SetoidObject := {|
  carrier   := Sets_limit_carrier;
  is_setoid := {| equiv := Sets_limit_equiv |}
|}.
Next Obligation.
  constructor.
  - intros p d; reflexivity.
  - intros p q Hpq d; symmetry; exact (Hpq d).
  - intros p q r Hpq Hqr d; transitivity (`1 q d);
    [exact (Hpq d)|exact (Hqr d)].
Qed.

(* The leg at [d]: evaluate a compatible family at [d]. *)
Program Definition Sets_limit_leg (d : D) : Sets_limit_obj ~{Sets}~> F d := {|
  morphism := fun p => `1 p d
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d). Qed.

(* The limit cone.  Its coherence condition is precisely the compatibility
   constraint carried by each family. *)
Program Definition Sets_limit_cone : Cone F := {|
  vertex_obj := Sets_limit_obj;
  coneFrom   := {| vertex_map := Sets_limit_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(* The mediator out of a competing cone [N]: bundle the legs of [N] at a
   point [e] into a family, whose compatibility is [N]'s own cone coherence
   read at [e]. *)
Program Definition Sets_limit_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> Sets_limit_obj := {|
  morphism := fun e =>
    (fun d => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e;
     fun d d' f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f e)
|}.
Next Obligation.
  intros N e e' Hee' d.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

Program Definition Sets_Limit : Limit F := {|
  limit_cone := Sets_limit_cone;
  ump_limits := fun N => {| unique_obj := Sets_limit_med N |}
|}.
Next Obligation. intros N d e; reflexivity. Qed.
Next Obligation. intros N v Hv e d; symmetry; exact (Hv d e). Qed.

End SetsLimit.

(* [Sets] is complete: every diagram of every shape has a limit.  See the
   header for the smallness discipline recorded on the universe context of
   this constant. *)
Definition Sets_Complete : @Complete Sets := fun D F => Sets_Limit F.

(** * Mac Lane's cone-set construction *)

(*
   本节说明 Complete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ConeSet.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Mac Lane's [Cone ( *, F)]: the cone presheaf of Structure/Cone.v
   evaluated at the terminal setoid.  Not a copy -- the two [eq_refl]
   Examples below pin both fields of the [SetoidObject]. *)
Definition cone_apex : obj[Sets] :=
  fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal).

Example cone_apex_is_ConePresheaf :
  cone_apex = fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal)
  := eq_refl.

Example cone_apex_carrier :
  carrier cone_apex = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

Example cone_apex_setoid :
  @is_setoid cone_apex = AConeEquiv (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

(* Display (2): [v_j : Cone ( *, F) --> F_j], [sigma |--> sigma_j].  The
   function sends a cone to the value of its leg at [d] on the one point. *)
Program Definition cone_leg_at (d : D) : cone_apex ~{Sets}~> F d := {|
  morphism := fun p => @vertex_map _ _ _ _ p d ttt
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d ttt). Qed.

(* The leg IS evaluation, on the nose. *)
Example cone_leg_at_is_evaluation (d : D) (p : cone_apex) :
  cone_leg_at d p = @vertex_map _ _ _ _ p d ttt := eq_refl.

(* "hence v as defined in (2) is a cone to the base F": the coherence of
   the cone of legs is the argument cone's own coherence at the point. *)
Program Definition cone_set_acone : ACone cone_apex F := {|
  vertex_map := cone_leg_at
|}.
Next Obligation.
  intros x y f p; exact (@cone_coherence _ _ _ _ p x y f ttt).
Qed.

Definition cone_set_cone : Cone F :=
  {| vertex_obj := cone_apex; coneFrom := cone_set_acone |}.

(* Mac Lane's [h]: "for each x in X, tau x is a cone to F from one point,
   so there is a unique function h : X --> Cone ( *, F) sending each x to
   tau x". *)
Program Definition cone_set_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> cone_apex := {|
  morphism := fun e =>
    {| vertex_map := fun d => {| morphism := fun _ =>
         @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e |} |}
|}.
Next Obligation. intros N e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros N e x y f u.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f e).
Qed.
Next Obligation.
  intros N e e' Hee' d u.
  exact (proper_morphism
           (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

(* Commuting is definitional. *)
Lemma cone_set_med_commutes (N : Cone F) (d : D) :
  cone_leg_at d ∘ cone_set_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d.
Proof. intros e; reflexivity. Qed.

(* Uniqueness.  The [destruct u] is the one use of the singleton's
   unique-inhabitant property in the whole construction. *)
Lemma cone_set_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> cone_apex) :
  (∀ d : D, cone_leg_at d ∘ v
              ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) →
  cone_set_med N ≈ v.
Proof. intros Hv e d u; destruct u; symmetry; exact (Hv d e). Qed.

(* Theorem 1, at the apex-pinned level. *)
Program Definition cone_set_IsALimit : IsALimit F cone_apex := {|
  limit_acone := cone_set_acone;
  ump_limit := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

(* Theorem 1, bundled. *)
Program Definition cone_set_Limit : Limit F := {|
  limit_cone := cone_set_cone;
  ump_limits := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

End ConeSet.

(* Completeness of [Set], by Mac Lane's own construction.  A second witness
   beside [Sets_Complete]; see the header for why both stand. *)
Definition ConeSet_Complete : @Complete Sets := fun D F => cone_set_Limit F.

(** ** Mac Lane's discrete example *)

(*
   本节说明笛卡尔、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition discrete_limit {A : Set} (f : A → obj[Sets]) :
  Limit (DiscreteCat_Functor f) := Sets_Limit (DiscreteCat_Functor f).

(* The limit's apex IS the compatible-family object of the discrete
   diagram. *)
Example discrete_apex_is_limit_obj {A : Set} (f : A → obj[Sets]) :
  iprod f (discrete_limit f)
  = Sets_limit_obj (DiscreteCat_Functor f) := eq_refl.

(* The product setoid it is cut out of IS literally [Sets_iprod_obj f]. *)
Example discrete_inner_is_iprod {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)
  = Sets_iprod_obj f := eq_refl.

(* The limit legs ARE the indexed-product projections. *)
Example discrete_leg_is_proj {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a
  = Sets_limit_leg (DiscreteCat_Functor f) a := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma discrete_compatible {A : Set} (f : A → obj[Sets])
  (x : Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)) :
  Sets_limit_compatible (DiscreteCat_Functor f) x.
Proof. intros d d' e; destruct e; simpl; reflexivity. Qed.

Program Definition discrete_forget {A : Set} (f : A → obj[Sets]) :
  Sets_limit_obj (DiscreteCat_Functor f) ~{Sets}~> Sets_iprod_obj f := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros A f p q Hpq a; exact (Hpq a). Qed.

Program Definition discrete_pair {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj f ~{Sets}~> Sets_limit_obj (DiscreteCat_Functor f) := {|
  morphism := fun x => (x; discrete_compatible f x)
|}.
Next Obligation. intros A f x y Hxy a; exact (Hxy a). Qed.

(* The discrete limit IS the cartesian product, up to isomorphism. *)
Program Definition discrete_iprod_iso {A : Set} (f : A → obj[Sets]) :
  @Isomorphism Sets (Sets_limit_obj (DiscreteCat_Functor f))
                    (Sets_iprod_obj f) := {|
  to := discrete_forget f; from := discrete_pair f
|}.
Next Obligation. intros A f x a; reflexivity. Qed.
Next Obligation. intros A f p a; reflexivity. Qed.

(* Both leg families, at the setoid grade.  The [eq_refl] form of the first
   is refused at CONVERSION and is pinned in the probe. *)
Lemma discrete_iprod_iso_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
    ≈ iprod_proj f (discrete_limit f) a.
Proof. intros p; reflexivity. Qed.

Lemma discrete_iprod_iso_leg_inv {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a ∘ from (discrete_iprod_iso f)
    ≈ Sets_iprod_proj f a.
Proof. intros x; reflexivity. Qed.
