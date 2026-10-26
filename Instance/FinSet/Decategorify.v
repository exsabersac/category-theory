Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.

From Coq Require Import Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * * Decategorifying the exponential laws: the groupoid of finite sets / * * 指数定律的去范畴化：有限集合的群范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/decategorification
 nLab: https://ncatlab.org/nlab/show/categorification
 nLab: https://ncatlab.org/nlab/show/FinSet

 Riehl, “Category Theory in Context”, §1.4 Example 1.4.11 (printed p. 29)
 reads the four exponential laws

 z^(x × y) ≅ (z^y)^x,           (y × z)^x ≅ y^x × z^x,
 x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

 in finite sets, and observes that on restricting to the GROUPOID of finite
 sets and bijections and applying the cardinality functor to the DISCRETE
 category of natural numbers, the four isomorphisms become the four
 arithmetic identities

 z^(xy) = (z^y)^x,   (yz)^x = y^x z^x,
 x(y+z) = xy + xz,   x^(y+z) = x^y x^z,

 so that the groupoid of finite sets is a categorification of ℕ.  The
 naturality half of the same example -- Mac Lane, “Categories for the
 Working Mathematician”, 2nd ed., §II.5 Exercise 2 (printed p. 44) -- is
 Structure/Cartesian/Closed/Natural.v.

 ** What is and is not the content here

 The four identities below are, as arithmetic, entirely elementary: [lia]
 proves the third outright and the other three follow by induction with
 [Nat.pow_mul_r], [Nat.pow_mul_l], [Nat.mul_add_distr_l] and
 [Nat.pow_add_r].  NONE of that is used.  Each identity is obtained by
 applying [FinSet_skeletal] -- equivalently, the arrow action of
 [Card_FinSet] -- to the CATEGORICAL isomorphism at [FinSet], so the route
 is the content: the equation of numbers is the shadow cast by an
 isomorphism of finite sets, and the proof term contains no arithmetic
 induction at all.

 ** Why two cardinality functors

 [Card_Groupoid] is Riehl's functor as stated: its domain is the groupoid
 of genuinely SET-LIKE objects (Instance/FinSet/Skeleton.v's [Set_f], finite
 setoids each carrying a chosen counting) and its arrow action discards the
 bijection, keeping only the fact that one exists -- which is exactly what
 decategorification does.

 [Card_FinSet] is its skeletal shadow: [FinSet] has the naturals themselves
 as objects (Instance/FinSet.v), so the functor is the identity on objects
 and its arrow action is [FinSet_skeletal].  It is the one the four
 identities are read off, because at [FinSet] the product, coproduct and
 exponential objects ARE [*], [+] and [^] on [nat]
 (Instance/FinSet/Product.v, Instance/FinSet.v, Instance/FinSet/Closed.v).

 ** A note on [=] versus [≈]

 The library's standing rule is that morphisms are compared with [≈], never
 with [=].  Nothing below breaks it: every [=] here is between OBJECTS.
 [FinSet]'s objects are natural numbers, and the hom-sets of
 [DiscreteCat nat] (Instance/Discrete.v) are equality PROOFS between
 naturals compared by [Morphism_equality], i.e. by [eq] on those proofs.
 That is why every functor law below is an identity between two proofs of
 one equation of naturals, discharged by Hedberg's theorem in its standard
 library form [UIP_dec] applied to [Nat.eq_dec] -- a theorem, not an axiom,
 so the whole file stays closed under the global context. 

 --------
 nLab: https://ncatlab.org/nlab/show/decategorification
 nLab: https://ncatlab.org/nlab/show/categorification
 nLab: https://ncatlab.org/nlab/show/FinSet

 Riehl，《语境中的范畴论》，§1.4 例 1.4.11（印刷页 29）
 列出了四个指数律

 z^(x × y) ≅ (z^y)^x,           (y × z)^x ≅ y^x × z^x,
 x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

 在有限集合中，并观察到，当限制在有限集合与双射的群oid上，并将基数函子应用于自然数的离散范畴时，这四个同构变为四个算术恒等式

 z^(xy) = (z^y)^x,   (yz)^x = y^x z^x,
 x(y+z) = xy + xz,   x^(y+z) = x^y x^z因此有限集合的群族是 ℕ 的一种范畴化。同一例子的自然性部分——Mac Lane，《为工作数学家而写的范畴论》，第二版，§II.5 练习 2（印刷版第 44 页）——是 Structure/Cartesian/Closed/Natural.v。

 ** 这里的内容是什么，什么不是下面的四个恒等式，从算术角度来看，完全是基础的：[lia] 直接证明了第三个，其余三个则通过归纳由 [Nat.pow_mul_r]、[Nat.pow_mul_l]、[Nat.mul_add_distr_l] 和 [Nat.pow_add_r] 得到。以上都没有被使用。每个恒等式都是通过应用 [FinSet_skeletal]——或者说，[Card_FinSet] 的箭头作用——到 [FinSet] 处的范畴同构而得到的，所以路径本身就是内容：数字的等式是有限集同构投射的影子，而证明项完全不包含任何算术归纳。  

 ** 为什么有两个基数函子[Card_Groupoid] 是 Riehl 的函子，如下所述：它的定义域是群范畴，即真正的集合类对象（Instance/FinSet/Skeleton.v 中的 [Set_f]，有限的集合体，每个都带有选定的计数），其箭头作用会丢弃双射，只保留存在这一事实——这正是去范畴化所做的。 

 [Card_FinSet] 是它的骨架影子：[FinSet] 将自然数本身作为对象（Instance/FinSet.v），所以函子在对象上是恒等的，它的箭头作用是 [FinSet_skeletal]。它就是从中读取四个恒等式的那个函子，因为在 [FinSet] 中，乘积、余积和指数对象正是 [*]、[+] 和 [^] 在 [nat] 上（Instance/FinSet/Product.v、Instance/FinSet.v、Instance/FinSet/Closed.v）。

 ** 关于 [=] 和 [≈] 的注释图书馆的既定规则是，态射总是与 [≈] 比较，从不与 [=] 比较。下面的内容没有违反这一规则：这里的每个 [=] 都是在 OBJECTS 之间的。[FinSet] 的对象是自然数，而 [DiscreteCat nat]（Instance/Discrete.v）的 Hom 集是在自然数之间按 [Morphism_equality] 比较的等式证明，即在那些证明上按 [eq] 比较。这就是为什么下面的每条函子定律都是两个关于自然数等式证明的恒等式，通过在 [Nat.eq_dec] 上应用其标准库形式 [UIP_dec] 的 Hedberg 定理得到——这是一个定理，而非公理，因此整个文件在全局上下文下保持封闭。
*)

(* * ** The cardinality functor on the groupoid of finite sets / * ** 有限集合群的基数函子 *)

(*
 The arrow action ignores WHICH bijection it is given and retains only the
 equality of countings that its existence forces.  That is the
 decategorification: a groupoid whose hom-sets can be large is mapped onto
 a discrete category whose hom-sets are subsingletons. 

 --------
 箭头作用忽略了给定的双射的具体类型，只保留其存在所强制的计数相等。这就是去范畴化：一个其同态集可以很大的群类被映射到一个同态集为子单集的离散范畴。
*)
Program Definition Card_Groupoid : Groupoid Set_f ⟶ DiscreteCat nat := {|
  fobj := setf_cardinality;
  fmap := fun A B i => setf_cardinality_iso_invariant A B i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(** ** The skeletal companion / ** 骨骼伙伴 *)

(*
 On the skeleton the object action is the identity: [FinSet]'s objects are
 already the naturals, and the whole functor is [FinSet_skeletal] read as an
 arrow action. 

 --------
 在骨架上，对象作用是恒等的：[FinSet] 的对象已经是自然数，并且整个函子被 [FinSet_skeletal] 读取为箭头作用。
*)
Program Definition Card_FinSet : Groupoid FinSet ⟶ DiscreteCat nat := {|
  fobj := fun n => n;
  fmap := fun m n i => @FinSet_skeletal m n i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(* The object action is the identity on the nose. / 对象操作正好是恒等映射。 *)
Example Card_FinSet_identity_on_objects (n : FinSet) :
  fobj[Card_FinSet] n = n := eq_refl.

(*
   * ** The four arithmetic identities, decategorified

   Each is the image under [Card_FinSet] of the corresponding categorical
   isomorphism, taken at [FinSet].  Orientations follow the in-tree object
   maps: [product_obj m n = (m * n)%nat] (Instance/FinSet/Product.v),
   [product_obj] of [FinSet_Cocartesian] -- the coproduct -- is
   [(m + n)%nat] (Instance/FinSet.v), and [exponent_obj m n = (n ^ m)%nat],
   so that [exponent_obj x z], displayed [z ^ x], is the object of functions
   FROM x (Instance/FinSet/Closed.v). 

   --------
   * ** 四则运算恒等式，去范畴化后的形式

   每一个都是相应范畴同构在 [FinSet] 下通过 [Card_FinSet] 的映射。方向遵循树状对象映射：[product_obj m n = (m * n)%nat]（Instance/FinSet/Product.v），[product_obj] 到 [FinSet_Cocartesian] —— 余积 —— 是 [(m + n)%nat]（Instance/FinSet.v），以及 [exponent_obj m n = (n ^ m)%nat]，因此 [exponent_obj x z]，显示为 [z ^ x]，是从 x 出发的函数对象（Instance/FinSet/Closed.v）。
*)

Definition nat_exp_prod_l (x y z : nat) : (z ^ (x * y))%nat = ((z ^ y) ^ x)%nat :=
  FinSet_skeletal (@exp_prod_l FinSet _ _ x y z).

Definition nat_exp_prod_r (x y z : nat) :
  ((y * z) ^ x)%nat = (y ^ x * z ^ x)%nat :=
  FinSet_skeletal (@exp_prod_r FinSet _ _ x y z).

Definition nat_prod_coprod_r (x y z : nat) :
  (x * (y + z))%nat = (x * y + x * z)%nat :=
  FinSet_skeletal (@prod_coprod_r FinSet _ _ _ x y z).

Definition nat_exp_coprod (x y z : nat) :
  (x ^ (y + z))%nat = (x ^ y * x ^ z)%nat :=
  FinSet_skeletal (@exp_coprod FinSet _ _ _ x y z).

(*
 Each identity IS the functor's action on the isomorphism; stated for one
 of the four, since [fmap[Card_FinSet]] is [FinSet_skeletal] by
 construction. 

 --------
 每一个恒等式都是函子在同构上的作用；对四个中的一个来说，由于构造，[fmap[Card_FinSet] 是 [FinSet_skeletal]。
*)
Example nat_exp_coprod_is_Card_image (x y z : nat) :
  nat_exp_coprod x y z = fmap[Card_FinSet] (@exp_coprod FinSet _ _ _ x y z)
  := eq_refl.

(*
   * ** Naturality decategorifies to nothing

   [DiscreteCat nat] is THIN: any two parallel arrows agree, because its
   hom-sets are equality proofs between naturals and [Nat.eq_dec] makes those
   unique.  So every naturality square in the image of a cardinality functor
   commutes for free, and the four natural isomorphisms of
   Structure/Cartesian/Closed/Natural.v have no shadow downstairs at all:
   what survives decategorification is the equation, not its naturality. 

   --------
   * ** 自然性去范畴化后变为无

   [DiscreteCat nat] 是 THIN：任意两条平行箭头都相同，因为它的同态集是自然数之间相等的证明，而 [Nat.eq_dec] 使这些证明唯一。因此，基数函子图像中的每个自然性平方自动交换，而且 Structure/Cartesian/Closed/Natural.v 中的四个自然同构在下层根本没有影子：去范畴化后存留下来的只是方程，而不是它的自然性。
*)
Lemma DiscreteCat_nat_Thin : Thin (DiscreteCat nat).
Proof. intros x y f g; apply (UIP_dec PeanoNat.Nat.eq_dec). Qed.

Corollary Card_FinSet_squares_commute {m n : FinSet}
          (i j : m ~{Groupoid FinSet}~> n) :
  fmap[Card_FinSet] i ≈ fmap[Card_FinSet] j.
Proof. apply DiscreteCat_nat_Thin. Qed.

(* * ** Sanity: the functors and the identities compute / * ** 理智：函子和恒等式进行计算 *)

(*
 [parity_two] (Instance/FinSet/Skeleton.v) is [nat] under equality of
 parity: an infinite carrier of cardinality 2. 

 --------
 [parity_two]（Instance/FinSet/Skeleton.v）在奇偶性相等下是 [nat]：一个基数为 2 的无限载体。
*)
Example card_groupoid_parity_two :
  fobj[Card_Groupoid] parity_two = 2%nat := eq_refl.

Example card_groupoid_incl_three :
  fobj[Card_Groupoid] (FinSet_Incl 3%nat) = 3%nat := eq_refl.

Example card_finset_five : fobj[Card_FinSet] 5%nat = 5%nat := eq_refl.

Example nat_exp_coprod_2_1_1 : (2 ^ (1 + 1))%nat = (2 ^ 1 * 2 ^ 1)%nat :=
  nat_exp_coprod 2%nat 1%nat 1%nat.

Example nat_exp_prod_l_2_3_2 : (2 ^ (3 * 2))%nat = ((2 ^ 2) ^ 3)%nat :=
  nat_exp_prod_l 3%nat 2%nat 2%nat.

Example nat_prod_coprod_r_4_2_3 : (4 * (2 + 3))%nat = (4 * 2 + 4 * 3)%nat :=
  nat_prod_coprod_r 4%nat 2%nat 3%nat.

Example nat_exp_prod_r_2_3_4 : ((3 * 4) ^ 2)%nat = (3 ^ 2 * 4 ^ 2)%nat :=
  nat_exp_prod_r 2%nat 3%nat 4%nat.
