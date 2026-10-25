Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * The opposite (dual) of a hom-set adjunction: F ⊣ U yields U^op ⊣ F^op.  / * hom-set 附加的相反（对偶）：F ⊣ U 产生 U^op ⊣ F^op。*)

(*
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U (here F : D ⟶ C left, U : C ⟶ D right) is given in
   hom-set form by a natural family adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y).
   Passing to opposite categories reverses every hom-set, so the left and right
   roles exchange: the dual is U^op ⊣ F^op, with U^op : C^op ⟶ D^op now the
   left adjoint and F^op : D^op ⟶ C^op the right adjoint. Concretely the dual
   iso at (x y), with x an object of C and y an object of D, has type
   (U^op x ~{D^op}~> y) ≊ (x ~{C^op}~> F^op y), which unfolds the reversed
   hom-sets to (y ~{D}~> U x) ≊ (F y ~{C}~> x). That is exactly the original
   adj at swapped arguments (y x), read backwards: so [to] of the dual is
   [from] of [adj y x] and [from] of the dual is [to] of [adj y x]. Both nLab
   (see its "Opposite adjoint functors" section) and Wikipedia state this
   flip; nLab phrases it as Hom_{D^op}(-, U^op -) ≃ Hom_{C^op}(F^op -, -).

   The four naturality fields transport accordingly. Because the dual swaps the
   two transposes (to ↔ from) and op reverses composition so the two hom-set
   arguments trade roles (left ↔ right), each field is supplied by the original
   field of the opposite kind and side: to_adj_nat_l from from_adj_nat_r,
   to_adj_nat_r from from_adj_nat_l, and dually for the from-side fields. 

--------
nLab：https://ncatlab.org/nlab/show/adjoint+functor
 维基百科：https://en.wikipedia.org/wiki/Adjoint_functors

附加词 F ⊣ U（这里 F : D ⟶ C 左，U : C ⟶ D 右）由下式给出：
 自然族 adj {x y} 的 hom 集形式：(F x ~{C}~> y) ≊ (x ~{D}~> U y)。 
传递到相反的类别会反转每个 hom-set，因此左侧和右侧
 角色交换：对偶是 U^op ⊣ F^op，U^op : C^op ⟶ D^op 现在是
 左伴随和 F^op : D^op ⟶ C^op 右伴随。 具体来说，双
 iso at (x y)，其中 x 是 C 的对象，y 是 D 的对象，具有类型
 (U^op x ~{D^op}~> y) ≊ (x ~{C^op}~> F^op y)，展开反转
 hom 集为 (y ~{D}~> U x) ≊ (F y ~{C}~> x)。 这正是原来的样子
 adj 在交换的参数 (y x) 处，向后读：所以对偶的 [to] 是
 [from]的[adj y x]和[from]的对偶是[to]的[adj y x]。 两个 nLab
 （参见“相反伴随”部分）并且维基百科声明了这一点
 翻转； nLab 将其表述为 Hom_{D^op}(-, U^op -) ≃ Hom_{C^op}(F^op -, -)。

四自然场相应地运输。 因为双交换
 两个转置（to ↔ from）和 op 反转组合，因此两个 hom-set
 参数交换角色（左↔右），每个字段均由原始字段提供
 相反种类和侧面的字段：来自 from_adj_nat_r 的 to_adj_nat_l，
 to_adj_nat_r 来自 from_adj_nat_l，并且双重用于 from-side 字段。 
*)

Program Definition Opposite_Adjunction `(F : D ⟶ C) `(U : C ⟶ D)
        (A : F ⊣ U) :
  U^op ⊣ F^op := {|
  adj := fun x y =>
    {| to          := from (@adj _ _ _ _ A y x)
     ; from        := to (@adj _ _ _ _ A y x)
     ; iso_to_from := iso_from_to (@adj _ _ _ _ A y x)
     ; iso_from_to := iso_to_from (@adj _ _ _ _ A y x) |};

  to_adj_nat_l   := fun _ _ _ f g => @from_adj_nat_r _ _ _ _ A _ _ _ g f;
  to_adj_nat_r   := fun _ _ _ f g => @from_adj_nat_l _ _ _ _ A _ _ _ g f;
  from_adj_nat_l := fun _ _ _ f g => @to_adj_nat_r  _ _ _ _ A _ _ _ g f;
  from_adj_nat_r := fun _ _ _ f g => @to_adj_nat_l  _ _ _ _ A _ _ _ g f
|}.

(* Mirrors the F^op notation on functors, at the same level/scope.  / 在同一级别/范围上反映函子上的 F^op 表示法。*)

Notation "N ^op" := (@Opposite_Adjunction _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : adjunction_scope.

Open Scope adjunction_scope.

(*
The op construction is an involution on adjunctions: since (C^op)^op = C and
   F^op reuse their underlying data on the nose, and the dual swaps the iso's
   to/from twice, applying op twice recovers A by [reflexivity]. 

--------
op 结构是附加词的对合：因为 (C^op)^op = C 且
 F^op在鼻子上重用它们的底层数据，并且双交换iso的
 往返两次，应用操作两次可通过 [reflexivity] 恢复 A。 
*)

Corollary Opposite_Adjunction_invol `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  (A^op)^op = A.
Proof. reflexivity. Qed.
