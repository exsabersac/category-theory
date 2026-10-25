Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Roof.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
   * * Preservation over a class of diagram shapes (Riehl §3.4)

   Riehl's Definition 3.4.1 speaks of functors preserving the limits of all
   diagrams "of a given shape, or of a given size" — a quantification the
   tree has had no vocabulary for: the per-diagram classes and the
   all-shapes ContinuousFunctor existed, with nothing between.  This file
   supplies the intermediate forms.  For products the shape class is the
   discrete categories; for FINITE limits the tree has had no finiteness
   predicate on shapes at all (Structure/Limit/Creation.v records the gap,
   and Structure/Topos.v spells "finite limits" as terminal + products +
   pullbacks instead).  [FiniteShape] is that predicate, in the enumeration
   form the setoid setting supports: finitely many objects, and finitely
   many arrows in each hom UP TO ≈.  The lists are data, so the record is a
   [Type] and its inhabitants compute; the three witnesses at the bottom —
   the empty shape, the discrete pair, and the walking span — are exactly
   the shapes whose limits are the terminal object, binary products and
   pullbacks, tying the new predicate to the topos-layer reading of
   "finitely complete". 

   --------
   * * 对一类图形形状的保持 (Riehl §3.4)Riehl的定义3.4.1提到函子保留所有“给定形状或给定大小”的图的极限——这是树状结构从未有过的量化表达：存在按图分类的类和所有形状的连续函子，但两者之间什么都没有。这个文件提供了中间形式。对于积，形状类是离散范畴；对于有限极限，树状结构根本没有关于形状的有限性断言（Structure/Limit/Creation.v记录了这一空白，而Structure/Topos.v将“有限极限”表述为终对象 + 积 + 拉回）。[FiniteShape]就是这个断言，在集合道具环境下的枚举形式：有限个对象，以及每个Hom中至多≈个箭头。这些列表是数据，所以记录是一个 [Type]，其居民进行计算；底部的三个见证——空形、离散对和行走跨度——正是其极限是终对象、二元积和拉回的形状，将新的谓词与“有限完备”的拓扑层阅读联系起来。
*)

(* * ** Products: the discrete-shape case / * ** 产品：离散形状的外壳 *)

Definition PreservesProductCones {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (A : Type) (K : DiscreteCat A ⟶ C), PreservesLimitCone K F.

Definition Continuous_PreservesProductCones {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesProductCones F :=
  fun A K => H (DiscreteCat A) K.

(** ** Finite shapes / ** 有限形状 *)

(*
 Structure/Limit/Finite.v's [FiniteCategory] is now the tree's finiteness
 predicate on shapes (Structure/Limit/Creation.v points at it;
 Structure/Topos.v and Structure/Regular.v once spelled "finite limits" as
 terminal, products, pullbacks).  A second, in the enumeration form of
 Construction/Subcategory/Finite.v and Construction/Free/Quiver/
 Presented.v: finitely many objects, and finitely many arrows in each
 hom UP TO [≈], which is the only reading the setoid setting supports.
 The lists are data, so the record is a [Type] and its inhabitants
 compute. 

 --------
 Structure/Limit/Finite.v 的 [FiniteCategory] 现在是树形的形状上的有限性谓词（Structure/Limit/Creation.v 指向它；Structure/Topos.v 和 Structure/Regular.v 曾将“有限极限”表示为终结对象、积、拉回）。第二种，在 Construction/Subcategory/Finite.v 和 Construction/Free/Quiver/Presented.v 的枚举形式中：有限多个对象，以及在每个 Hom 中有限多条箭头，直至 [≈]，这是集合化环境支持的唯一解释。这些列表是数据，所以记录是一个 [Type]，并且其元素可以计算。
*)

Record FiniteShape (J : Category) : Type := {
  fs_objs : list (obj[J]);
  fs_objs_all : ∀ x : obj[J], List.In x fs_objs;
  fs_homs : ∀ x y : obj[J], list (x ~{J}~> y);
  fs_homs_all : ∀ (x y : obj[J]) (f : x ~{J}~> y),
    { g : x ~{J}~> y & prod (List.In g (fs_homs x y)) (g ≈ f) }
}.

Arguments fs_objs {J} _.
Arguments fs_objs_all {J} _ _.
Arguments fs_homs {J} _ _ _.
Arguments fs_homs_all {J} _ _ _ _.

Definition PreservesFiniteLimitCones {C D : Category} (F : C ⟶ D) : Type :=
  PreservesLimitConesOver FiniteShape F.

Definition Continuous_PreservesFiniteLimitCones {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesFiniteLimitCones F :=
  Continuous_PreservesLimitConesOver H.

Definition PreservesFiniteLimitCones_OfShape {C D : Category} {F : C ⟶ D}
  (H : PreservesFiniteLimitCones F) {J : Category} (HJ : FiniteShape J) :
  PreservesLimitConesOfShape J F := H J HJ.

(** ** The predicate is inhabited / ** 谓词是有含义的 *)

(*
 The global obligation tactic preprocesses these goals unpredictably;
 take manual control (precedent: Functor/Structure/Monoidal/Id.v). 

 --------
 全球义务策略会不可预测地预处理这些目标；
 手动控制（先例：Functor/Structure/Monoidal/Id.v）。
*)
#[local] Obligation Tactic := idtac.

Program Definition FiniteShape_0 : FiniteShape _0 := {|
  fs_objs := nil; fs_homs := fun _ _ => nil |}.
Next Obligation. intros x; destruct x. Qed.
Next Obligation. intros x; destruct x. Qed.

Program Definition FiniteShape_Two_Discrete : FiniteShape Two_Discrete := {|
  fs_objs := TwoDX :: TwoDY :: nil;
  fs_homs := fun x y =>
    match x, y return list (x ~{Two_Discrete}~> y) with
    | TwoDX, TwoDX => TwoDIdX :: nil
    | TwoDY, TwoDY => TwoDIdY :: nil
    | _, _ => nil
    end |}.
Next Obligation. intros x; destruct x; simpl; auto. Qed.
Next Obligation.
  intros x y f; destruct x, y.
  - exists TwoDIdX; split;
      [ simpl; auto | symmetry; exact (TwoDHom_inv _ _ f) ].
  - exact (False_rect _ (TwoDHom_X_Y_absurd f)).
  - exact (False_rect _ (TwoDHom_Y_X_absurd f)).
  - exists TwoDIdY; split;
      [ simpl; auto | symmetry; exact (TwoDHom_inv _ _ f) ].
Qed.

Program Definition FiniteShape_Roof : FiniteShape Roof := {|
  fs_objs := RNeg :: RZero :: RPos :: nil;
  fs_homs := fun x y =>
    match x, y return list (x ~{Roof}~> y) with
    | RNeg,  RNeg  => IdNeg   :: nil
    | RZero, RNeg  => ZeroNeg :: nil
    | RZero, RZero => IdZero  :: nil
    | RZero, RPos  => ZeroPos :: nil
    | RPos,  RPos  => IdPos   :: nil
    | _, _ => nil
    end |}.
Next Obligation. intros x; destruct x; simpl; auto. Qed.
Next Obligation.
  intros x y f; destruct x, y.
  - exists IdNeg; split; [ simpl; auto | constructor ].
  - exact (False_rect _ (RNeg_RZero_absurd f)).
  - exact (False_rect _ (RNeg_RPos_absurd f)).
  - exists ZeroNeg; split; [ simpl; auto | constructor ].
  - exists IdZero; split; [ simpl; auto | constructor ].
  - exists ZeroPos; split; [ simpl; auto | constructor ].
  - exact (False_rect _ (RPos_RNeg_absurd f)).
  - exact (False_rect _ (RPos_RZero_absurd f)).
  - exists IdPos; split; [ simpl; auto | constructor ].
Qed.
