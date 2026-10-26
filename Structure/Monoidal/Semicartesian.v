Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section SemicartesianMonoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia: no dedicated article; the notion is described under
 https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 A semicartesian (also affine) monoidal category is a monoidal category
 whose unit object I is terminal. Spelled out in this library's notation,
 that is the pair of conditions

 eliminate      : x ~> I             (a map into I for every x),
 unit_terminal  : f ≈ g              (any two x ~> I agree),

 so that I has exactly one map from each object: it is terminal. It is
 strictly weaker than cartesian monoidal, where the tensor is the
 categorical product; here only the discard maps into I are guaranteed,
 not the diagonals (cartesian = semicartesian + coherent diagonals). The
 internal logic is affine logic: weakening (discarding) but not in general
 contraction (copying).

 The terminality of I equips every tensor with projection maps, defined
 exactly as on nLab from a discard on one factor and the matching unitor,

 proj_left  = rho    ∘ (id ⨂ eliminate) : x ⨂ y ~> x,
 proj_right = lambda ∘ (eliminate ⨂ id) : x ⨂ y ~> y. 

 --------
 nLab:  https://ncatlab.org/nlab/show/semicartesian+monoidal+category 
 维基百科：没有专门的文章；该概念在 https://en.wikipedia.org/wiki/Cartesian_monoidal_category 下有描述

 半笛卡尔（也称仿射）幺半群范畴是指其单位对象 I 为终对象的幺半群范畴。用本库的符号表示，即为以下条件对：

 eliminate      : x ~> I             （每个 x 到 I 的映射），
 unit_terminal  : f ≈ g              （任意两个 x ~> I 的映射相等），

 因此，每个对象到 I 都有且只有一个映射：I 是终对象。这比笛卡尔幺半群范畴严格弱，其中张量是范畴积；在这里只能保证废弃映射到 I，而不是对角映射（笛卡尔 = 半笛卡尔 + 相容的对角映射）。其内部逻辑是仿射逻辑：允许削弱（丢弃），但不一定允许收缩（复制）。I 的终端性为每个张量配备了投影映射，定义方式完全如 nLab 上所示：从一个因子上的消去（discard）和匹配的单位子（unitor）得到，

 proj_left  = rho    ∘ (id ⨂ 消去) : x ⨂ y ~> x,
 proj_right = lambda ∘ (消去 ⨂ id) : x ⨂ y ~> y。
*)

Class SemicartesianMonoidal `{@Monoidal C} := {
  (* the discard / projection-to-unit map, the unique x ~> I / 丢弃 / 投影到单位的映射，唯一的 x ~> I *)
  eliminate {x} : x ~> I;

  (* uniqueness of maps into I, i.e. I is terminal (up to ≈) / 映射到 I 的唯一性，即 I 是终对象（直到 ≈） *)
  unit_terminal {x} (f g : x ~> I) : f ≈ g;

  (* left projection x ⨂ y ~> x: discard y, then the right unitor / 左投影 x ⨂ y ~> x：丢弃 y，然后右幺元子 *)
  proj_left  {x y} : x ⨂ y ~> x := unit_right ∘ id ⨂ eliminate;
  (* right projection x ⨂ y ~> y: discard x, then the left unitor / 右投影 x ⨂ y ~> y：丢弃 x，然后左单位器 *)
  proj_right {x y} : x ⨂ y ~> y := unit_left  ∘ eliminate ⨂ id
}.

(* Discarding after any map is discarding: eliminate is natural, since both sides are maps A ~> I and I is terminal. / 在任何映射之后丢弃就是丢弃：消除是自然的，因为两边都是映射 A ~> I 且 I 是终端对象。 *)

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

End SemicartesianMonoidal.

Require Import Category.Structure.Terminal.

(*
 The two directions below witness that “semicartesian monoidal” and “the
 unit I is terminal” are the same condition, packaged as a Terminal
 structure on I and as a SemicartesianMonoidal structure respectively. Cf.
 Wikipedia, https://en.wikipedia.org/wiki/Cartesian_monoidal_category :
 “in any such category, the terminal object is the monoidal unit.” 

 --------
 以下两个方向证明了“半笛卡尔幺半群”和“单位对象 I 是终对象”是相同的条件，分别作为 I 上的终结构和作为半笛卡尔幺半群结构。参见维基百科，https://en.wikipedia.org/wiki/Cartesian_monoidal_category：“在任何这样的范畴中，终对象都是幺半群单位对象。”
*)

(*
 Semicartesian monoidal ==> I is a terminal object, with eliminate as the
 unique arrow and unit_terminal as its uniqueness proof. 

 --------
 半笛卡尔单体范畴 ==> I 是一个终对象，eliminate 是唯一箭头，unit_terminal 是其唯一性证明。
*)

Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
        `{@SemicartesianMonoidal C _} : @Terminal C := {|
  terminal_obj := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

Import EqNotations.

(*
 Conversely, a monoidal category whose terminal object 1 coincides with the
 unit object I (the hypothesis Heq : 1 = I) is semicartesian monoidal:
 transport the unique arrow `one` along Heq to obtain eliminate, and
 transport one_unique to obtain unit_terminal. 

 --------
 相反，一个终对象1与单位对象I重合的单模范畴（假设 Heq : 1 = I）是半笛卡尔单模范畴：沿 Heq 传送唯一箭头 `one` 以获得 eliminate，并传送 one_unique 以获得 unit_terminal。
*)

Program Definition Terminal_SemicartesianMonoidal `{M : @Monoidal C}
        `{T : @Terminal C} (Heq : 1 = @I C M) :
  @SemicartesianMonoidal C _ := {|
  eliminate := fun x => rew Heq in one;
  unit_terminal := fun x f g =>
    _ (one_unique (rew <- Heq in f) (rew <- Heq in g))
|}.
Next Obligation.
  unfold eq_rect_r, eq_rect, eq_sym in x.
  destruct Heq.
  assumption.
Defined.
