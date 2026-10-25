Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The free bicartesian closed category, presented syntactically. / 自由双笛卡尔闭范畴，语法上呈现。 *)

(*
 nLab: https://ncatlab.org/nlab/show/free+cartesian+category
 nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

 A bicartesian closed category is a cartesian closed category that also has
 finite coproducts (an initial object and binary coproducts); its internal
 language is the simply-typed lambda calculus with sums. This file builds the
 free such category on no generators as a term model: objects [Obj] are the
 syntax of types and morphisms [Hom a b] are the syntax of arrows (abstract
 syntax trees) built from the bicartesian-closed combinators.

 Following the term-model construction (nLab: free cartesian category),
 composition is the syntactic constructor [Compose] and the product/coproduct
 structure is given by the pairing/copairing constructors. Rather than quotient
 the terms by βη-equality directly, two arrows are deemed equivalent when they
 agree under *every* interpretation into a concrete bicartesian closed category:

 f ≈ g  :=  ∀ C (bicartesian closed), interp f ≈ interp g     ([AST] homset)

 This makes [interp] sound by construction and, because the free category is
 initial among bicartesian closed categories, the relation coincides with
 equality of arrows in the free BiCCC. The result is the canonical setting for
 normalising/deciding equations of bicartesian-closed combinators (a solver:
 prove an equation once in [AST] and it holds in every model). 

 --------
 nLab:  https://ncatlab.org/nlab/show/free+cartesian+category 
 nLab:  https://ncatlab.org/nlab/show/bicartesian+closed+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Cartesian_closed_category 

 一个双笛卡尔闭范畴是一个笛卡尔闭范畴，同时也具有有限余积（一个初始对象和二元余积）；它的内部语言是具有和的简单类型λ演算。此文件以项模型建立在没有生成元的情况下的自由此类范畴：对象 [Obj] 是类型的语法，态射 [Hom a b] 是从双笛卡尔闭组合子构建的箭头语法（抽象语法树）。按照项模型构造（nLab：自由笛卡尔范畴），组合是语法构造子 [Compose]，积/余积结构由配对/共配对构造子给出。与其直接通过 βη-等式来取项的商，不如当两个箭头在*每一个*具体双笛卡尔闭范畴的解释下都一致时，认为它们是等价的：

 f ≈ g  :=  ∀ C（双笛卡尔闭），interp f ≈ interp g     ([AST] 同态集)这使得 [interp] 在构造上发声，并且由于自由范畴在双笛卡尔闭范畴中是初始的，该关系与自由 BiCCC 中箭头的相等性一致。其结果是双笛卡尔闭组合子方程归一化/判定的规范设置（一个求解器：只需在 [AST] 中证明一次方程，它就适用于每个模型）。
*)

#[local] Obligation Tactic := cat_simpl.

(*
 The syntax of objects: the closed type formers of a bicartesian closed
 category (1, ×, ^, 0, +). [denote] reads each former off in a model C. 

 --------
 对象的语法：双笛卡尔闭类别 (1, ×, ^, 0, +) 的封闭类型构造子。[denote] 在模型 C 中读取每个构造子。
*)
Inductive Obj : Set :=
  | One_    : Obj                       (* terminal object 1 / 末端对象 1 *)
  | Prod_   : Obj → Obj → Obj           (* product x × y / 积 x × y *)
  | Exp_    : Obj → Obj → Obj           (* exponential, [Exp_ x y] = y ^ x / 指数，[Exp_ x y] = y ^ x *)
  | Zero_   : Obj                       (* initial object 0 / 初始对象 0 *)
  | Coprod_ : Obj → Obj → Obj.          (* coproduct x + y / 余积 x + y *)

(*
 Interpretation of object syntax into a bicartesian closed category C:
 each type former is read off using the corresponding structure of C. 

 --------
 将对象语法解释为双笛卡尔闭范畴 C：每个类型构造子都使用 C 的对应结构来读取。
*)
Fixpoint denote `(o : Obj) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_        => 1
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => 0
  | Coprod_ x y => denote x + denote y
  end.

(*
 The syntax of arrows: one constructor per bicartesian-closed combinator.
 This is a typed term language (a GADT indexed by source and target object),
 so every well-formed AST denotes a morphism via [interp] below. 

 --------
 箭头的语法：每个二笛卡尔封闭组合子对应一个构造函数。 这是一个类型化的项语言（一个由源对象和目标对象索引的GADT）， 因此每个良构的AST都通过下方的 [interp] 表示一个态射。
*)
Inductive Hom : Obj → Obj → Set :=
  | Id      : ∀ {a}, Hom a a                                     (* identity id / 身份证 *)
  | Compose : ∀ {a b c}, Hom b c → Hom a b → Hom a c             (* composition g ∘ f / 复合函数 g ∘ f *)

  | One'    : ∀ {a}, Hom a One_                                  (* terminal map ! : a ~> 1 / 终端地图 ! : a ~> 1 *)

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a                         (* projection exl / 投影 EXL *)
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b                         (* projection exr / 投影 EXR *)
  | Fork    : ∀ {a c d}, Hom a c → Hom a d → Hom a (Prod_ c d)   (* pairing ⟨f, g⟩ / 配对 ⟨f, g⟩ *)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c → Hom a (Exp_ b c)    (* transpose curry / 换位咖喱 *)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) → Hom (Prod_ a b) c    (* inverse transpose uncurry / 逆转置 取消柯里化 *)

  | Zero'   : ∀ {a}, Hom Zero_ a                                 (* initial map ¡ : 0 ~> a / 初始映射 ¡ : 0 ~> a *)

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)                       (* injection inl / 注射inl *)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)                       (* injection inr / 注射用INR *)
  | Merge   : ∀ {a c d}, Hom c a → Hom d a → Hom (Coprod_ c d) a. (* copairing [f, g] / 配对 [f, g] *)

(*
 Interpretation of arrow syntax into a bicartesian closed category C: each
 combinator is sent to the corresponding operation of C, so [interp] is the
 unique structure-preserving functor out of the free category into any model. 

 --------
 将箭头语法解释为双笛卡尔闭范畴 C：每个组合子都被映射到 C 的相应运算，因此 [interp] 是从自由范畴到任何模型的唯一保持结构的函子。
*)
Program Fixpoint interp `(c : Hom a b) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
  match c with
  | Id          => id
  | Compose f g => interp f ∘ interp g

  | One'        => one

  | Exl         => exl
  | Exr         => exr
  | Fork f g    => fork (interp f) (interp g)

  | Curry f     => curry (interp f)
  | Uncurry f   => uncurry (interp f)

  | Zero'       => zero

  | Inl         => inl
  | Inr         => inr
  | Merge f g   => merge (interp f) (interp g)
  end.

(*
 The free bicartesian closed category: objects are [Obj], arrows are [Hom],
 identity and composition are the syntactic constructors, and two arrows are
 equivalent when they agree under every interpretation (see the file header).
 That equivalence is an equivalence relation [Next Obligation] and is a
 congruence for composition (proven for [Hom_Cartesian] etc. below). 

 --------
 自由双笛卡尔闭类别：对象为 [Obj]，箭头为 [Hom]，恒等和复合是语法构造，并且当两个箭头在每个解释下都一致时，它们被认为是等价的（参见文件头）。这种等价关系是一个等价关系 [Next Obligation]，并且是复合的模（在下面对 [Hom_Cartesian] 等进行了证明）。
*)
#[export]
Program Instance AST : Category := {
  obj     := Obj;
  hom     := Hom;
  id      := @Id;
  compose := @Compose;
  homset  := fun _ _ =>
    {| equiv := fun f g =>
         ∀ (C : Category)
                (A : @Cartesian C)
                `(@Closed C A)
                `(@Cocartesian C)
                `(@Terminal C)
                `(@Initial C),
           interp f ≈ interp g |}
}.
Next Obligation.
  equivalence.
  transitivity (interp y); auto.
Qed.

(* Terminal object 1 = [One_], with the unique arrow into it given by [One']. / 终端对象 1 = [One_]，它的唯一箭头由 [One'] 给出。 *)
#[export]
Program Instance Hom_Terminal : @Terminal AST := {
  terminal_obj := One_;
  one := @One'
}.
Next Obligation. apply one_unique. Qed.

(*
 Binary products x × y = [Prod_], with pairing [Fork] and projections
 [Exl]/[Exr]; the universal property holds under every interpretation. 

 --------
 二元积 x × y = [Prod_]，配对 [Fork] 以及投影 [Exl] / [Exr]；在每个解释下都满足泛性质。
*)
#[export]
Program Instance Hom_Cartesian : @Cartesian AST := {
  product_obj := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
  - split; intros; rewrite HA; cat.
  - intros.
    destruct HA as [? ?].
    rewrite <- e, <- e0.
    rewrite fork_comp; cat.
Qed.

(*
 Exponentials z ^ y = [Exp_], with the currying isomorphism realised by the
 mutually-inverse syntactic transposes [Curry] and [Uncurry]. 

 --------
 指数表达式 z ^ y = [Exp_]，使用互为逆的语法转置 [Curry] 和 [Uncurry] 实现柯里化同构。
*)
#[export]
Program Instance Hom_Closed : @Closed AST _ := {
  exponent_obj := Exp_;
  exp_iso := fun x y z =>
    {| to   := {| morphism := @Curry x y z |}
     ; from := {| morphism := @Uncurry x y z |} |}
}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.

(*
 Initial object 0 = [Zero_], with the unique arrow [Zero'] out of it. Since
 [Initial AST] unfolds to [Terminal (AST^op)] (duality idiom), this fills the
 dual fields [terminal_obj]/[one], which on the C-side read as initial_obj/zero. 

 --------
 初始对象 0 = [Zero_]，具有唯一箭头 [Zero'] 指向它。由于 [Initial AST] 展开为 [Terminal (AST^op)]（对偶惯用法），这填充了对偶字段 [terminal_obj] / [one]，在 C 端读取为 initial_obj/zero。
*)
#[export]
Program Instance Hom_Initial : @Initial AST := {
  terminal_obj := Zero_;
  one := @Zero'
}.
Next Obligation. apply zero_unique. Qed.

(*
 Binary coproducts x + y = [Coprod_], with copairing [Merge] and injections
 [Inl]/[Inr]. As [Cocartesian AST] unfolds to [Cartesian (AST^op)] (duality
 idiom), the cartesian fields [fork]/[exl]/[exr] are filled by the dual
 combinators, recovering merge/inl/inr on the C-side. 

 --------
 二元余积 x + y = [Coprod_]，伴随对映 [Merge] 以及注入 [Inl] / [Inr]。随着 [Cocartesian AST] 展开为 [Cartesian (AST^op)]（对偶习语），笛卡尔场 [fork] / [exl] / [exr] 被对偶组合子填充，在 C 端恢复 merge/inl/inr。
*)
#[export]
Program Instance Hom_Cocartesian : @Cocartesian AST := {
  product_obj := Coprod_;
  fork := @Merge;
  exl  := @Inl;
  exr  := @Inr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
  - split; intros; rewrite HA; cat.
  - intros.
    destruct HA as [? ?].
    rewrite <- e, <- e0.
    rewrite merge_comp; cat.
Qed.

(*
 [interp] respects arrow equivalence: equivalent ASTs interpret to equivalent
 morphisms in C. This is immediate, since the homset equivalence of [AST] is
 precisely agreement under every interpretation, instantiated here at C. 

 --------
 [interp] 尊重箭头等价：等价的 AST 在 C 中解释为等价的态射。这是显而易见的，因为 [AST] 的 hom 集等价正是每个解释下的一致性，这里在 C 中实例化。
*)
#[export]
Program Instance interp_proper {x y : Obj}
        {C : Category} {A : @Cartesian C}
        `{@Closed C A} `{@Cocartesian C}
        `{@Terminal C} `{@Initial C} :
  Proper (@equiv _ (@homset AST x y) ==>
                     @equiv _ (@homset C _ _))
         (fun f => @interp x y f C A _ _ _ _).
