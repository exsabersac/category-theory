Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* * * From weakly initial family genuine 始对象 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件记录 Freyd 一般伴随函子定理的对象层输入：从*弱*初始族到真正初始对象的通路。
   族 [wif_obj : wif_index -> C] 弱初始，当每个对象 [c] 被某成员击中，即 [wif_cover c]
   展示指标 [i] 与箭头 [wif_obj i ~> c]（存在性，无唯一性）。经典构造（Freyd，
   Mac Lane CWM V.6）形成该族的积 [P]——本身是单个弱初始对象——再挖出 [P] *全部*
   自同态的联合等化子；该等化子真正初始。

   状态 / 假设形式。构造恰消耗两个在调用方选定指标 [Type] 上的极限，以及二元等化子供给：

     - [P]  ：族 [wif_obj] 在 [wif_index] 上的积
              （指标积 = 离散图的极限）；
     - [Pe] ：在该积对象自同态的 hom 类型上，该对象与自身的积——这是 [Type]-指标极限，
              其普遍锥使单个平行对 [P ~> Pe]「一次捕获全部自同态」，故自同态族的宽等化子
              归约为 [E] 供给的一个*二元*等化子；
     - [E]  ：平行对的二元等化子。

   两积作为显式假设传入，而非从 [Complete] / [HasIndexedProducts] 实例收获。这是刻意的
   （Risk (b)）：自同态指标积量化在 hom 类型 [iprod .. ~> iprod ..] 上，坐在 hom 宇宙 [h]；
   经量化每个指标 [Type] 的类路由会过度承诺环境宇宙，而显式形式把指标的小性（故相关宇宙约束）
   留给调用方。把 [Pe] 与 [P] 分开供给加强假设（诚实、更瘦的输入），从不削弱结论，结论仍是
   完整 [Initial C]。

   [Pe] 的族是常数——[fun _ : P0 ~> P0 => P0]——故 [Pe] 是 Mac Lane III.3/III.4 意义下
   [P0] 的幂，下文经 Structure/Limit/Power.v 的 [power_of_limit]、[power_ev_of_limit]、
   [power_ump_of_limit] 如此说明。它们是常数族上的 [iprod]、[iprod_proj]、[iprod_ump]，
   由 [:=] 供给，故变化靠转换，定理陈述不受影响——[Pe] 的类型上文写全且未动。[P] 的族
   [wif_obj W] 真正变化，仍是指标积。仅 Require Structure/Limit/Power.v，非其
   Structure/Limit/Power/Hom.v 卫星；[Instance/Sets] 本就在本文件闭包中（测得：自 #435
   起两跳，Instance/Parallel → Instance/Sets；此前三跳）。 *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record WeaklyInitialFamily (C : Category) := {
  wif_index : Type;
  wif_obj : wif_index -> C;
  wif_cover (c : C) : { i : wif_index & wif_obj i ~> c }
}.

Arguments wif_index {C} _.
Arguments wif_obj {C} _ _.
Arguments wif_cover {C} _ _.

(*
   本节说明等化子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明（余）极限、hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem initial_from_weakly_initial@{lim idx obj h +}
  {C : Category@{obj h h}} (W : WeaklyInitialFamily@{idx obj h} C)
  (P : Limit@{lim idx h obj} (DiscreteCat_Functor (wif_obj W)))
  (Pe : Limit@{h h h obj}
          (DiscreteCat_Functor
             (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
              => iprod (wif_obj W) P)))
  (E : HasEqualizers C) : @Initial C.
Proof.
  (* Abbreviate product 对象 fold it [Pe]'s index. （已译） *)
  set (P0 := iprod (wif_obj W) P) in *.

  (* Weak initiality of [P0]: a chosen map into every object.  [wif_obj W] is
     a genuinely varying family, so this stays an indexed PRODUCT; it is only
     [Pe] below whose family is constant. *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  destruct (power_ump_of_limit P0 Pe P0 (fun u => u)) as [m Hm0 _].
  destruct (power_ump_of_limit P0 Pe P0 (fun _ => id[P0])) as [d Hd0 _].
  (* beta-normalized reads of the two universal families *)
  assert (Hm : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ m ≈ u)
    by exact Hm0.
  assert (Hd : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ d ≈ id[P0])
    by exact Hd0.

  (* 相关说明。 （已译） *)
  destruct (@equalizer C E P0 (power_of_limit P0 Pe) m d) as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizer inclusion. *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    assert (Hu : power_ev_of_limit P0 Pe u ∘ (m ∘ e)
                   ≈ power_ev_of_limit P0 Pe u ∘ (d ∘ e)).
    { rewrite (fork_eq Eeq); reflexivity. }
    rewrite !comp_assoc in Hu.
    rewrite (Hm u) in Hu.
    rewrite (Hd u) in Hu.
    transitivity (id[P0] ∘ e).
    + exact Hu.
    + apply id_left. }

  (* The equalizer inclusion is monic. *)
  pose proof (equalizer_monic m d Eeq) as Me.
  destruct Me as [mon].

  (* Assemble the initial object as a terminal object of [C^op]. *)
  unshelve refine (@Build_Terminal (C^op) I _ _).
  - (* existence: [I ~> x] via weak initiality post-composed with [e] *)
    intro x.
    exact (wmap x ∘ e).
  - (* uniqueness: any two [f g : I ~> x] agree *)
    intros x f g.
    (* read goal [C]: [f], [g] [C]-态射 [I ~> x] （已译） *)
    change (unop f ≈ unop g).
    (* 相关说明。 （已译） *)
    destruct (@equalizer C E I x f g) as [K [k Ek]].
    (* weak initiality supplies a map [P0 ~> K] *)
    pose (s := wmap K).
    (* [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then cancels it, exhibiting [s ∘ e] as a section of [k]. *)
    assert (Habs : (e ∘ (k ∘ s)) ∘ e ≈ e ∘ id[I]).
    { transitivity e.
      - exact (endo_absorb (e ∘ (k ∘ s))).
      - symmetry; apply id_right. }
    assert (Hk : (k ∘ s) ∘ e ≈ id[I]).
    { apply (mon _ ((k ∘ s) ∘ e) (id[I])).
      transitivity ((e ∘ (k ∘ s)) ∘ e).
      - apply comp_assoc.
      - exact Habs. }
    (* hence [k ∘ (s ∘ e) ≈ id]: [k] is a split epimorphism *)
    assert (Hkr : k ∘ (s ∘ e) ≈ id[I]).
    { transitivity ((k ∘ s) ∘ e).
      - apply comp_assoc.
      - exact Hk. }
    (* 相关说明。 （已译） *)
    transitivity (unop f ∘ (k ∘ (s ∘ e))).
    + transitivity (unop f ∘ id[I]).
      * symmetry; apply id_right.
      * apply compose_respects; [ reflexivity | symmetry; exact Hkr ].
    + transitivity (unop g ∘ (k ∘ (s ∘ e))).
      * transitivity ((unop f ∘ k) ∘ (s ∘ e)).
        -- apply comp_assoc.
        -- transitivity ((unop g ∘ k) ∘ (s ∘ e)).
           ++ apply compose_respects; [ exact (fork_eq Ek) | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Require Import Category.Structure.Complete.
Require Import Category.Instance.Parallel.

(* * ** A weakly 始对象 (Riehl Definition 4.7.4) （已译） *)

(* One 对象 arrow every 对象, no uniqueness. A weakly
 initial family jointly weakly initial version: [wif_cover] picks
 own member per target. （已译） *)
Definition WeaklyInitial {C : Category} (c : C) : Type := ∀ x : C, c ~> x.

Definition weakly_initial_obj_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitial (@initial_obj C I) := fun x => @zero C I x.

Definition wif_of_weakly_initial {C : Category} {c : C} (w : WeaklyInitial c) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => c
   ; wif_cover := fun x => (ttt; w x) |}.

(* The product weakly initial family weakly 始对象: the
 [wmap] 证明 above builds inline, now named. （已译） *)
Definition weakly_initial_iprod {C : Category} (W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W))) :
  WeaklyInitial (iprod (wif_obj W) P) :=
  fun c => projT2 (wif_cover W c)
             ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c)).

(* * ** Necessity: 始对象 singleton weakly initial family （已译） *)

(* 相关说明。 （已译） *)
Definition weakly_initial_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => @initial_obj C I
   ; wif_cover := fun x => (ttt; @zero C I x) |}.

(* The family built 始对象, nose. （已译） *)
Example weakly_initial_of_initial_index {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = poly_unit := eq_refl.

Example weakly_initial_of_initial_obj {C : Category} (I : @Initial C)
  (u : poly_unit) :
  wif_obj (weakly_initial_of_initial I) u = @initial_obj C I := eq_refl.

Example weakly_initial_of_initial_cover {C : Category} (I : @Initial C)
  (x : C) :
  projT2 (wif_cover (weakly_initial_of_initial I) x) = @zero C I x := eq_refl.

(** ** The biconditional *)

(* 相关说明。 （已译） *)
Definition FreydProducts (C : Category) : Type :=
  ∀ W : WeaklyInitialFamily C,
    { P : Limit (DiscreteCat_Functor (wif_obj W))
    & Limit (DiscreteCat_Functor
               (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P
                => iprod (wif_obj W) P)) }.

(* 相关说明。 （已译） *)
Definition initial_iff_weakly_initial_family {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - intro W.
    destruct (Ps W) as [P Pe].
    exact (initial_from_weakly_initial W P Pe E).
Defined.

Example initial_iff_weakly_initial_family_fst {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family Ps E) I = weakly_initial_of_initial I
  := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition initial_from_weakly_initial_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (W : WeaklyInitialFamily C) :
  @Initial C :=
  initial_from_weakly_initial W
    (HC (DiscreteCat (wif_index W)) (DiscreteCat_Functor (wif_obj W)))
    (HC (DiscreteCat _)
        (DiscreteCat_Functor
           (fun _ : iprod (wif_obj W)
                      (HC (DiscreteCat (wif_index W))
                          (DiscreteCat_Functor (wif_obj W)))
                    ~> iprod (wif_obj W)
                         (HC (DiscreteCat (wif_index W))
                             (DiscreteCat_Functor (wif_obj W)))
            => iprod (wif_obj W)
                 (HC (DiscreteCat (wif_index W))
                     (DiscreteCat_Functor (wif_obj W))))))
    E.

Definition initial_iff_weakly_initial_family_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - exact (initial_from_weakly_initial_complete HC E).
Defined.

Example initial_iff_weakly_initial_family_complete_fst {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family_complete HC E) I
    = weakly_initial_of_initial I := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Parallel_ParX_WeaklyInitial : @WeaklyInitial Parallel ParX :=
  fun x => match x with
           | ParX => (true; ParIdX)
           | ParY => (true; ParOne)
           end.

Theorem Parallel_ParX_not_initial : @IsInitialObj Parallel ParX → False.
Proof.
  intro H.
  pose proof (@is_initial_unique Parallel ParX H ParY
                (true; ParOne) (false; ParTwo)) as E.
  simpl in E.
  discriminate E.
Qed.

Theorem Parallel_ParY_not_weakly_initial :
  @WeaklyInitial Parallel ParY → False.
Proof.
  intro w.
  destruct (w ParX) as [b h].
  exact (ParHom_Y_X_absurd b h).
Qed.
