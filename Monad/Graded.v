Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Graded monads  / * 分级单子*)

(*
nLab: https://ncatlab.org/nlab/show/graded+monad

   Graded monads (also called parametric monads).  Fix an ordinary monoid
   (E, ε, ·) of "grades" — here a [GradeMonoid], a record over a Coq type with
   the monoid laws stated in propositional equality [=].  An E-graded monad on
   a category C is a family of endofunctors  T : E → (C ⟶ C)  together with a
   unit

     gret : x ~> T ε x

   and a family of graded multiplications

     gjoin : T m (T n x) ~> T (m · n) x

   satisfying the monad laws up to the monoid's associativity and unit
   equations, which are transported along the family by the cast morphisms
   [gcast] below.  Grades typically track a quantitative effect discipline:
   which effects may occur, how many times, at what cost.

   Honest formulation.  The class [GradedMonad] below mirrors Theory/Monad.v
   field-for-field: [gret] and [gjoin] generalize [ret] and [join], and the
   five laws [gfmap_ret], [gjoin_fmap_join], [gjoin_fmap_ret], [gjoin_ret],
   [gjoin_fmap_fmap] generalize the five monad laws, each mediated by a
   [gcast] along the corresponding grade-monoid equation.  At the trivial
   one-element grading every [gcast] reduces to [id] and the five laws are
   literally the five laws of Theory/Monad.v; the bridges [GradedMonad_Monad]
   and [Monad_GradedMonad_const] below make this degeneracy precise in both
   directions, with definitional round-trips ([roundtrip_ret],
   [roundtrip_join]).

   Relation to the monoid picture.  Monad/Monoid.v ([Monoid_Monad]) exhibits
   an ordinary monad as a monoid object in the endofunctor category [C, C]
   under composition.  A graded monad likewise has a delooping reading: it is
   a lax functor from B E — the one-object bicategory whose 1-cells are the
   elements of E, composed by ·, with only identity 2-cells — to the
   one-object bicategory delooping the strict monoidal category
   ([C, C], ◯, Id).  The unique object goes to the unique object, the 1-cell
   m goes to the endofunctor T m, and the lax coherence 2-cells are exactly
   [gret] (unit comparison, Id ⟹ T ε) and [gjoin] (composition comparison,
   T m ◯ T n ⟹ T (m · n)), natural by [gfmap_ret] and [gjoin_fmap_fmap].
   Equivalently: a lax monoidal functor into ([C, C], ◯, Id) from E read as a
   discrete strict monoidal category — objects the grades, tensor ·, unit ε —
   sending the object m to T m.  Bicategories, deloopings and lax monoidal
   functors are outside the scope of this file, so that equivalent reading is
   recorded here as prose only; the record below is the elementary spelling
   of the same data. 

--------
nLab：https://ncatlab.org/nlab/show/graded+monad

分级单子（也称为参数单子）。 修复一个普通的幺半群
 (E, ε, ·) 的“等级” — 这里是 [GradeMonoid]，Coq 类型的记录
 命题等式 [=] 中规定的幺半群定律。 E 级单子
 类别 C 是一个内函子族 T : E → (C ⟶ C) 以及 a
 单位

: x ~> T ε x

以及一系列分级乘法

gjoin : T m (T n x) ~> T (m · n) x

满足幺半群的结合律和单位的单子定律
 方程，通过强制态射沿族传输
 下面是 [gcast]。 成绩通常跟踪定量效应学科：
 可能会发生哪些影响、发生多少次、代价是什么。

诚实的表述。 下面的类 [GradedMonad] 镜像 Theory/Monad.v
 场对场：[gret] 和 [gjoin] 概括了 [ret] 和 [join]，并且
 五定律 [gfmap_ret]、[gjoin_fmap_join]、[gjoin_fmap_ret]、[gjoin_ret]、
 [gjoin_fmap_fmap] 概括了五个单子定律，每个定律都由一个
 [gcast] 沿着相应的等级幺半群方程。 在琐碎的事上
 每个 [gcast] 的单元素分级可简化为 [id]，五个定律是
 字面意思是 Theory/Monad.v 的五定律； 桥梁 [GradedMonad_Monad]
 下面的 [Monad_GradedMonad_const] 使这种简并性在以下两个方面都变得精确
 方向，具有定义的往返行程（[roundtrip_ret]，
 [roundtrip_join]）。

与幺半群图片的关系。 Monad/Monoid.v ([Monoid_Monad]) 展示
 一个普通的 monad 作为 endofunctor 类别 [C, C] 中的 monoid 对象
 下组成。 分级单子同样有一个解环解读：它是
 来自 B E 的松散函子 — 单对象二类别，其 1 单元格是
 E 的元素，由 · 组成，仅具有身份 2 细胞 — 到
 单对象二类别解环严格的幺半群范畴
 （[C, C]，◯，同上）。 唯一的对象转到唯一的对象，1-cell
 m 到达内函子 T m，松散的相干性 2 细胞正好是
 [gret]（单位比较，Id ⟹ T ε）和 [gjoin]（成分比较，
 T m ◯ T n ⟹ T (m · n))，由 [gfmap_ret] 和 [gjoin_fmap_fmap] 自然得出。 
等价地：将 E 中的松散幺半群函子读为 ([C, C], ◯, Id)
 离散严格幺半群范畴 — 对象的等级，张量·，单位 ε —
 将对象 m 发送到 T m。 双类别、去循环和松散幺半群
 函子超出了该文件的范围，因此等效的读取是
 此处仅以散文形式记录； 下面的记录是初级拼写
 相同的数据。 
*)

(*
The grade monoid: a plain monoid on a Coq type, with associativity and the
   two unit laws stated in propositional equality [=].

   NOTE on transparency: concrete instances should supply TRANSPARENT
   match-term proofs of the three laws (rather than opaque lemmas from the
   standard library such as [andb_assoc]), so that [gcast] computes to [id]
   on closed grades by mere reduction.  Alternatively, over a grade type with
   decidable equality any closed proof can be rewritten to [eq_refl] via
   [Eqdep_dec.UIP_dec], which by Hedberg's theorem is fully constructive and
   assumes nothing beyond the core theory; the transparent route taken below
   ([Trivial_GradeMonoid], [AndGrade]) avoids that extra step. 

--------
等级幺半群：Coq 类型上的普通幺半群，具有结合性和
 命题等式 [=] 中规定了两个单位定律。 

关于透明度的注意事项：具体实例应提供 TRANSPARENT
 三个定律的匹配项证明（而不是来自
 标准库（例如 [andb_assoc]），以便 [gcast] 计算为 [id]
 在封闭等级上仅通过减少。 或者，在等级类型上使用
 可判定的相等性任何封闭证明都可以通过重写为 [eq_refl]
 [Eqdep_dec.UIP_dec]，根据赫德伯格定理，它是完全构造性的并且
 不假设任何超出核心理论的内容； 下面采取的透明路线
 （[Trivial_GradeMonoid]、[AndGrade]）避免了这个额外的步骤。 
*)

Record GradeMonoid : Type := {
  grade :> Type;                        (* the underlying type of grades  / 成绩的基础类型*)
  gunit : grade;                        (* the neutral grade ε  / 中性等级 ε*)
  gmul : grade → grade → grade;         (* grade composition m · n *)

  gmul_assoc {a b c : grade} : gmul (gmul a b) c = gmul a (gmul b c);
  gmul_unit_l {a : grade} : gmul gunit a = a;
  gmul_unit_r {a : grade} : gmul a gunit = a
}.

Section Graded.

Context {C : Category}.
Context {E : GradeMonoid}.
Context {T : E → C ⟶ C}.

(*
Transport of a graded carrier along an equality of grades.  This is the
   only place where the propositional grade equations touch the morphisms:
   every law of [GradedMonad] is stated up to such a cast.  Defined as a
   direct match so it computes to [id] whenever the proof reduces to
   [eq_refl]. 

--------
沿等坡度运输分级载体。 这是
 命题级方程唯一接触态射的地方：
 [GradedMonad] 的每一条法则都是针对这样的转换而规定的。 定义为
 直接匹配，因此只要证明简化为，它就会计算为 [id]
 [eq_refl]。 
*)

Definition gcast {m n : E} (e : m = n) {x : C} : T m x ~> T n x :=
  match e in _ = k return T m x ~> T k x with
  | eq_refl => id
  end.

Lemma gcast_refl {m : E} {x : C} : @gcast m m eq_refl x ≈ id.
Proof. reflexivity. Qed.

Lemma gcast_trans {m n p : E} (e1 : m = n) (e2 : n = p) {x : C} :
  gcast e2 ∘ @gcast m n e1 x ≈ gcast (eq_trans e1 e2).
Proof. destruct e2, e1; simpl; cat. Qed.

(*
[gcast] is natural in the object variable: it commutes with the functorial
   action of the graded carriers. 

--------
[gcast] 在对象变量中是自然的：它与函子交换
 分级载体的作用。 
*)
Lemma gcast_natural {m n : E} (e : m = n) {x y : C} (f : x ~> y) :
  gcast e ∘ fmap[T m] f ≈ fmap[T n] f ∘ @gcast m n e x.
Proof. destruct e; simpl; cat. Qed.

(*
The E-graded monad, mirroring Theory/Monad.v field-for-field.  [gret] is
   the unit η at the neutral grade, [gjoin] the grade-multiplying μ, and the
   five laws are the five laws of [Monad] with every grade equation
   transported by [gcast].  At the trivial grading every cast is [id] and the
   laws collapse to the ungraded ones (see [GradedMonad_Monad] below). 

--------
E-graded monad，逐场镜像 Theory/Monad.v。 [gret] 是
 中性等级的单位 η，[gjoin] 等级乘法 μ，以及
 五个定律是 [Monad] 的五个定律与每个等级方程
 由 [gcast] 运输。 在琐碎的分级中，每个演员都是 [id]，并且
 法律崩溃为未分级的法律（请参阅下面的 [GradedMonad_Monad]）。 
*)

Class GradedMonad := {
  gret {x : C} : x ~> T (gunit E) x;                       (* graded unit η *)
  gjoin {m n : E} {x : C} : T m (T n x) ~> T (gmul E m n) x;   (* graded μ *)

  (* naturality of the unit η: gret ∘ f ≈ fmap f ∘ gret  / 单位 η 的自然性：灰色 ≈ ∘ 灰色的映射*)
  gfmap_ret {x y : C} (f : x ~> y) :
    gret ∘ f ≈ fmap[T (gunit E)] f ∘ gret;

  (* graded associativity: μ ∘ Tμ ≈ μ ∘ μT, up to gmul_assoc  / 分级关联性：μ ∘ Tμ ≈ μ ∘ μT，最高为 gmul_assoc*)
  gjoin_fmap_join {m n p : E} {x : C} :
    gjoin ∘ fmap[T m] (@gjoin n p x)
      ≈ gcast (gmul_assoc E) ∘ @gjoin (gmul E m n) p x ∘ @gjoin m n (T p x);

  (* graded left unit law: μ ∘ Tη ≈ id, up to gmul_unit_r  / 分级左单位定律：μ ∘ Tη ≈ id，直至 gmul_unit_r*)
  gjoin_fmap_ret {m : E} {x : C} :
    gjoin ∘ fmap[T m] (@gret x) ≈ gcast (eq_sym (gmul_unit_r E));

  (* graded right unit law: μ ∘ ηT ≈ id, up to gmul_unit_l  / 分级右单位定律：μ ∘ ηT ≈ id，直至 gmul_unit_l*)
  gjoin_ret {m : E} {x : C} :
    gjoin ∘ @gret (T m x) ≈ gcast (eq_sym (gmul_unit_l E));

  (* naturality of the multiplication μ  / 乘法 μ 的自然性*)
  gjoin_fmap_fmap {m n : E} {x y : C} (f : x ~> y) :
    gjoin ∘ fmap[T m] (fmap[T n] f) ≈ fmap[T (gmul E m n)] f ∘ gjoin
}.

End Graded.

Arguments GradedMonad {C} E T.

(*
Over a constant family the cast is always the identity, whatever the grade
   equation was: the transport happens in a family that does not move. 

--------
在一个固定的家庭中，无论等级如何，演员阵容始终是身份
 等式是：运输发生在一个不搬家的家庭中。 
*)
Lemma gcast_const {C : Category} {E : GradeMonoid} {M : C ⟶ C}
      {m n : E} (e : m = n) {x : C} :
  @gcast C E (fun _ => M) m n e x ≈ id.
Proof. destruct e; reflexivity. Qed.

(** ** The degenerate-grading bridge  / ** 简并分级桥*)

(*
The one-element grade monoid.  All three law proofs are transparent
   match-terms reducing to [eq_refl] on [ttt], so at this grading [gcast]
   is definitionally [id]. 

--------
单元素级幺半群。 三项法律证明都是透明的
 [ttt] 上的匹配项减少为 [eq_refl]，因此在此分级中 [gcast]
 定义为 [id]。 
*)
Definition Trivial_GradeMonoid : GradeMonoid := {|
  grade := poly_unit;
  gunit := ttt;
  gmul := fun _ _ => ttt;
  gmul_assoc := fun _ _ _ => eq_refl;
  gmul_unit_l := fun a => match a as u return ttt = u with ttt => eq_refl end;
  gmul_unit_r := fun a => match a as u return ttt = u with ttt => eq_refl end
|}.

#[local] Obligation Tactic := idtac.

(*
A trivially graded monad is an ordinary monad: every grade proof reduces
   to [eq_refl] definitionally, so every [gcast] reduces to [id], and the
   graded laws are the ungraded ones (the unit laws by direct conversion, the
   associativity law after erasing the identity cast). 

--------
一个平凡分级的单子是一个普通的单子：每个等级证明都会减少
 定义为 [eq_refl]，因此每个 [gcast] 都简化为 [id]，并且
 分级定律是未分级的定律（通过直接转换的单位定律，
 擦除身份转换后的结合律）。 
*)
Program Definition GradedMonad_Monad {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) : @Monad C M := {|
  ret  := fun x => @gret C Trivial_GradeMonoid (fun _ => M) G x;
  join := fun x => @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x
|}.
Next Obligation. (* fmap_ret *)
  intros C M G x y f.
  exact (@gfmap_ret C Trivial_GradeMonoid (fun _ => M) G x y f).
Qed.
Next Obligation. (* join_fmap_join *)
  intros C M G x.
  etransitivity.
  - exact (@gjoin_fmap_join C Trivial_GradeMonoid (fun _ => M) G ttt ttt ttt x).
  - rewrite gcast_const; cat.
Qed.
Next Obligation. (* join_fmap_ret: the cast is definitionally [id] here  / join_fmap_ret：这里的转换定义为 [id]*)
  intros C M G x.
  exact (@gjoin_fmap_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_ret: the cast is definitionally [id] here  / join_ret：这里的强制转换定义为 [id]*)
  intros C M G x.
  exact (@gjoin_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_fmap_fmap *)
  intros C M G x y f.
  exact (@gjoin_fmap_fmap C Trivial_GradeMonoid (fun _ => M) G ttt ttt x y f).
Qed.

(*
Conversely, any ordinary monad is E-graded for ANY grade monoid E, as the
   constant family at its endofunctor: all casts are erased by [gcast_const].
   Instantiating E with [Trivial_GradeMonoid] gives the inverse direction of
   the degenerate bridge, so this construction subsumes it. 

--------
相反，任何普通单子对于任何等级幺半群 E 都是 E 级的，因为
 其endofunctor处的常量族：所有类型转换都被[gcast_const]删除。 
用 [Trivial_GradeMonoid] 实例化 E 给出反方向
 退化的桥梁，所以这个建筑包含了它。 
*)
Program Definition Monad_GradedMonad_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (E : GradeMonoid) : @GradedMonad C E (fun _ => M) := {|
  gret  := fun x => @ret C M H x;
  gjoin := fun _ _ x => @join C M H x
|}.
Next Obligation. (* gfmap_ret *)
  intros C M H E x y f.
  exact (@fmap_ret C M H x y f).
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros C M H E m n p x.
  rewrite gcast_const, id_left.
  exact (@join_fmap_join C M H x).
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_fmap_ret C M H x).
Qed.
Next Obligation. (* gjoin_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_ret C M H x).
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros C M H E m n x y f.
  exact (@join_fmap_fmap C M H x y f).
Qed.

(*
Round-trips at the trivial grading hold definitionally: passing through
   either bridge leaves the structure maps unchanged. 

--------
琐碎等级的往返定义为：通过
 任一桥都保持结构图不变。 
*)

Corollary roundtrip_ret {C : Category} {M : C ⟶ C} (H : @Monad C M) (x : C) :
  @gret C Trivial_GradeMonoid (fun _ => M)
        (Monad_GradedMonad_const H Trivial_GradeMonoid) x ≈ @ret C M H x.
Proof. reflexivity. Qed.

Corollary roundtrip_join {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @join C M (GradedMonad_Monad G) x
    ≈ @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x.
Proof. reflexivity. Qed.

Corollary roundtrip_ret_trivial {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @ret C M (GradedMonad_Monad G) x
    ≈ @gret C Trivial_GradeMonoid (fun _ => M) G x.
Proof. reflexivity. Qed.

Corollary roundtrip_join_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (x : C) :
  @gjoin C Trivial_GradeMonoid (fun _ => M)
         (Monad_GradedMonad_const H Trivial_GradeMonoid) ttt ttt x
    ≈ @join C M H x.
Proof. reflexivity. Qed.

(** ** A nontrivial instance: the bool-graded exception monad over Coq  / ** 一个重要的实例：Coq 上的 bool 分级异常 monad*)

(*
The grade monoid (bool, true, andb): grade [true] means "pure so far"
   (no exception can have been raised), grade [false] means an exception may
   have been raised.  A composite computation is pure exactly when both
   stages are, whence [andb].  The law proofs are transparent match-terms so
   that [gcast] reduces on both constructors. 

--------
等级幺半群（bool、true 和b）：等级 [true] 表示“到目前为止纯”
 （不能提出异常），[false] 级意味着可能会出现异常
 已被提出。 当两者都满足时，复合计算是纯粹的
 [andb] 就是从这里开始的。 法律证明是透明的匹配项，因此
 [gcast] 在两个构造函数上都减少了。 
*)
Definition AndGrade : GradeMonoid := {|
  grade := bool;
  gunit := true;
  gmul := andb;
  gmul_assoc := fun a b c =>
    match a as a0 return andb (andb a0 b) c = andb a0 (andb b c) with
    | true  => eq_refl
    | false => eq_refl
    end;
  gmul_unit_l := fun a => eq_refl;
  gmul_unit_r := fun a =>
    match a as a0 return andb a0 true = a0 with
    | true  => eq_refl
    | false => eq_refl
    end
|}.

(*
The option endofunctor on Coq, defined locally as a categorical functor
   (Theory/Coq covers the programming-style classes instead). 

--------
Coq 上的选项 endofunctor，本地定义为分类函子
 （Theory/Coq 涵盖了编程风格的类）。 
*)
Program Definition option_Functor : Coq ⟶ Coq := {|
  fobj := option;
  fmap := fun _ _ f o => option_map f o
|}.
Next Obligation. (* fmap_respects *)
  intros x y f g Hfg [a|]; simpl; [rewrite Hfg|]; reflexivity.
Qed.
Next Obligation. (* fmap_id *)
  intros x [a|]; reflexivity.
Qed.
Next Obligation. (* fmap_comp *)
  intros x y z f g [a|]; reflexivity.
Qed.

(*
The graded carrier: at the pure grade the identity functor, at the
   impure grade [option]. 

--------
分级载体：在纯等级上恒等函子，在
 非纯级 [option]。 
*)
Definition ExcT (b : bool) : Coq ⟶ Coq :=
  if b then Id[Coq] else option_Functor.

(* The graded unit lives at grade [true], where the carrier is [Id].  / 分级单元位于 [true] 等级，其中载体为 [Id]。*)
Definition exc_ret (x : Type) : x → ExcT true x := fun a => a.

(*
The graded multiplication.  At (true, _) and (false, true) one of the two
   layers is the identity functor and the multiplication is the evident
   reindexing; at (false, false) it is the usual option join. 

--------
分级乘法。 在 (true, _) 和 (false, true) 两者之一
 层是恒等函子，乘法是明显的
 重新索引； at (false, false) 是常用的连接选项。 
*)
Definition exc_join (b1 b2 : bool) (x : Type) :
  ExcT b1 (ExcT b2 x) → ExcT (andb b1 b2) x :=
  match b1 as a, b2 as b return ExcT a (ExcT b x) → ExcT (andb a b) x with
  | true, _      => fun o => o
  | false, true  => fun o => o
  | false, false => fun o => match o with
                             | Some v => v
                             | None   => None
                             end
  end.

(*
The laws are proven by destructing the grades first — after which every
   [gcast] reduces to [id], by transparency of the [AndGrade] proofs — and
   then by pointwise case analysis in Coq's pointwise-equality homsets. 

--------
这些定律是通过首先破坏成绩来证明的——之后每一个
 通过 [AndGrade] 证明的透明度，[gcast] 简化为 [id] — 并且
 然后通过 Coq 的逐点相等 homset 中的逐点案例分析。 
*)
Program Definition Exc_GradedMonad : @GradedMonad Coq AndGrade ExcT := {|
  gret  := exc_ret;
  gjoin := exc_join
|}.
Next Obligation. (* gfmap_ret *)
  intros x y f a; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros m n p x; destruct m, n, p; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros m n x y f; destruct m, n; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.

(** ** The grade-only writer  / ** 只限年级的作家*)

(*
Pure grade tracking with trivial data: for ANY grade monoid W, the
   constant family at the identity functor is W-graded.  All structure maps
   are identities; every law is a [gcast] transport erased by [gcast_const].
   This is the "writer into W" whose entire log lives in the grades. 

--------
使用琐碎数据进行纯等级跟踪：对于任何等级幺半群 W，
 恒等函子处的常数族是 W 级的。 所有结构图
 是身份； 每个定律都是由 [gcast_const] 擦除的 [gcast] 传输。 
这是“W 作家”，他的整个日志都存在于成绩中。 
*)
Program Definition GradedWriter (W : GradeMonoid) :
  @GradedMonad Coq W (fun _ => Id[Coq]) := {|
  gret  := fun x (a : x) => a;
  gjoin := fun _ _ x (a : x) => a
|}.
Next Obligation. (* gfmap_ret *)
  intros W x y f; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros W m n p x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros W m n x y f; reflexivity.
Qed.
