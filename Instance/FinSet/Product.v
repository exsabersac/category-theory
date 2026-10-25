Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   * * Computable products on skeletal FinSet

   The product of the canonical m-element and n-element sets is the
   canonical (m * n)-element set, mediated by the standard base-n
   positional codec: the pair (a, b) is encoded as the digit string
   "a then b", i.e. the number a·n + b.  Both directions are structural
   fixpoints in the closed-computation style of [fin_split]/[fin_join]
   from [Instance/FinSet.v] — built only from [Fin.L], [Fin.R] and
   [fin_split], primitives available on every supported Coq/Rocq
   version — so pairings and projections REDUCE on closed inputs by
   [eq_refl].

   Since [Nat.mul] recurses as [S m' * n = n + m' * n], the encoding of
   (F1, b) is the first block [Fin.L (m' * n) b], and encoding along
   [Fin.FS] skips one block via [Fin.R n]. 

   --------
   * * 可计算的骨架有限集上的积

   标准的 m 元和 n 元集合的积是标准的 (m * n) 元集合，通过标准的基数 n 位编码器调解：对 (a, b) 的编码为数字字符串“a 然后 b”，即数 a·n + b。两个方向都是 [fin_split] / [fin_join] 在 [Instance/FinSet.v] 中封闭计算风格的结构性不动点 — 仅由每个支持的 Coq/Rocq 版本可用的 [Fin.L]、[Fin.R] 和 [fin_split] 原语构建 — 因此，成对和投影在封闭输入上通过 [eq_refl] 进行简化。

   由于 [Nat.mul] 按 [S m' * n = n + m' * n] 递归，（F1, b）的编码是第一个块 [Fin.L (m' * n) b]，而沿 [Fin.FS] 的编码通过 [Fin.R n] 跳过一个块。
*)

(*
   * [fin_pair a b] encodes the pair (a, b) as position a·n + b of the
   canonical (m * n)-element set, by structural recursion on [a]. 

   --------
   *  [fin_pair a b] 将一对 (a, b) 编码为规范的 (m * n) 元集合的第 a·n + b 个位置，通过对 [a] 的结构递归实现。
*)
Fixpoint fin_pair {m n : nat} (a : Fin.t m) : Fin.t n → Fin.t (m * n) :=
  match a in Fin.t m return Fin.t n → Fin.t (m * n) with
  | @Fin.F1 m' => fun b => Fin.L (m' * n) b
  | @Fin.FS m' a' => fun b => Fin.R n (fin_pair a' b)
  end.

(*
   * [fin_unpair] decodes a position of the canonical (m * n)-element set
   into its quotient/remainder pair, by structural recursion on [m]:
   each step peels one n-element block off through [fin_split]. 

   --------
   * [fin_unpair] 将一个规范的 (m * n) 元集合的位置解码为其商/余数对，这是通过对 [m] 的结构递归实现的：每一步通过 [fin_split] 剥离一个 n 元块。
*)
Fixpoint fin_unpair {m n : nat} {struct m} :
  Fin.t (m * n) → (Fin.t m * Fin.t n)%type :=
  match m return Fin.t (m * n) → (Fin.t m * Fin.t n)%type with
  | O => fun p => Fin.case0 (fun _ => (Fin.t 0 * Fin.t n)%type) p
  | S m' => fun p =>
      match @fin_split n (m' * n) p with
      | Datatypes.inl b => (Fin.F1, b)
      | Datatypes.inr q =>
          let '(a, b) := @fin_unpair m' n q in (Fin.FS a, b)
      end
  end.

(* The computability acceptance test: the codec reduces by [eq_refl]. With m = 2, n = 3 the pair (1, 1) sits at position 1·3 + 1 = 4. / 可计算性接受测试：编解码器减少了 [eq_refl]。 当 m = 2，n = 3 时，数对 (1, 1) 位于位置 1·3 + 1 = 4。 *)
Example fin_pair_computes :
  @fin_pair 2 3 (Fin.FS Fin.F1) (Fin.FS Fin.F1)
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

Example fin_unpair_computes :
  @fin_unpair 2 3 (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = (Fin.FS Fin.F1, Fin.FS Fin.F1) := eq_refl.

(*
   * ** The round trips

   Equality here is Leibniz equality on [Fin.t] VALUES — object-level
   data of the skeletal category, matching the pointwise-[eq] hom-setoid
   of [FinSet]. 

   --------
   * ** 往返旅行

   此处的等价性是 [Fin.t] 值上的莱布尼茨等价 — 骨架范畴的对象级数据，匹配 [FinSet] 的逐点 [eq] 同类集合。
*)

Lemma fin_unpair_pair {m n : nat} (a : Fin.t m) (b : Fin.t n) :
  fin_unpair (fin_pair a b) = (a, b).
Proof.
  induction a as [m' | m' a IH]; simpl.
  - (* (F1, b) is the first block: split lands left. / (F1, b) 是第一个方块：分裂格局在左边。 *)
    rewrite fin_split_L; reflexivity.
  - (* (FS a, b) skips one block: split lands right, then recurse. / (FS a, b) 跳过一个区块：先将土地分到右边，然后递归。 *)
    rewrite fin_split_R, IH; reflexivity.
Qed.

Lemma fin_pair_unpair {m n : nat} (p : Fin.t (m * n)) :
  fin_pair (fst (fin_unpair p)) (snd (fin_unpair p)) = p.
Proof.
  induction m as [| m' IH].
  - exact (Fin.case0
             (fun p : Fin.t 0 =>
                @fin_pair 0 n (fst (@fin_unpair 0 n p))
                              (snd (@fin_unpair 0 n p)) = p)
             p).
  - (* The scrutinee is spelled with explicit implicits so that it matches the occurrence [simpl] exposes in the goal. / 被检查项使用显式隐式拼写，以便它与目标中 [simpl] 暴露的出现匹配。 *)
    simpl; destruct (@fin_split n (m' * n) p) as [b | q] eqn:Hs.
    + (* p decodes as (F1, b): re-encoding is the left injection, and [fin_join_split] identifies it with p. / p 解码为 (F1, b)：重新编码是左注入，而 [fin_join_split] 将其与 p 关联。 *)
      simpl; rewrite <- (@fin_join_split n (m' * n) p), Hs; reflexivity.
    + (* p decodes through the recursive call on the tail q. / p 通过对尾部 q 的递归调用进行解码。 *)
      specialize (IH q).
      destruct (@fin_unpair m' n q) as [a b]; simpl in IH.
      simpl; rewrite IH, <- (@fin_join_split n (m' * n) p), Hs.
      reflexivity.
Qed.

(*
   * ** The cartesian structure

   The product object is [m * n], pairing is pointwise [fin_pair], and
   the projections are the components of [fin_unpair]; the universal
   property is exactly the two round trips, pointwise. 

   --------
   * ** 笛卡尔结构

   积对象是 [m * n]，配对是逐点 [fin_pair]，
   投影是 [fin_unpair] 的各个分量；
   普遍性正是两个逐点的往返映射。
*)

#[export] Program Instance FinSet_Cartesian : @Cartesian FinSet := {|
  product_obj := fun m n => (m * n)%nat;
  fork := fun x y z (f : Fin.t x → Fin.t y) (g : Fin.t x → Fin.t z) i =>
    fin_pair (f i) (g i);
  exl := fun y z (p : Fin.t (y * z)) => fst (fin_unpair p);
  exr := fun y z (p : Fin.t (y * z)) => snd (fin_unpair p)
|}.
Next Obligation.
  (* The pairing respects pointwise equality in both arguments. / 配对在两个参数中都尊重逐点相等。 *)
  intros f f' Hf g g' Hg i.
  rewrite (Hf i), (Hg i); reflexivity.
Qed.
Next Obligation.
  (*
 The universal property: h ≈ ⟨f, g⟩ exactly when the two decodings of
 h recover f and g — pointwise, by the round trips. 

 --------
 泛性质：当且仅当对 h 的两次解码能够恢复 f 和 g——逐点地，通过往返操作，h ≈ ⟨f, g⟩。
*)
  split.
  - intros Hh; split; intro i; simpl;
      rewrite (Hh i), fin_unpair_pair; reflexivity.
  - intros [Hl Hr] i.
    rewrite <- (Hl i), <- (Hr i), fin_pair_unpair; reflexivity.
Qed.

(*
 Closed pairings evaluated at concrete elements, by [eq_refl]: the fork
 of the two projections out of Fin.t 6 = Fin.t (2 * 3) re-encodes each
 element to itself, checked here at position 4 = (1, 1). 

 --------
 在具体元素上评估的闭合配对，由 [eq_refl] 提出：从 Fin.t 6 = Fin.t (2 * 3) 的两个投影所构成的叉子将每个元素重新编码为自身，这里在位置 4 = (1, 1) 进行了检查。
*)
Example fork_computes :
  @fork FinSet FinSet_Cartesian 6%nat 2%nat 3%nat
    (fun p : Fin.t 6 => fst (@fin_unpair 2 3 p))
    (fun p : Fin.t 6 => snd (@fin_unpair 2 3 p))
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

(*
   * ** Alignment with the terminal object

   The product with the chosen terminal object [1] of [FinSet_Terminal]
   lands on the nat [1 * n] (resp. [n * 1]), which is the object [n]
   itself: a propositional equality of OBJECTS of the skeletal category
   (nat values), recorded for downstream files that need to transport
   along the unitors on the nose. 

   --------
   * ** 与终端对象的对齐

   与所选终端对象 [1] 的 [FinSet_Terminal] 的积落在 nat [1 * n]（分别是 [n * 1]），它就是对象 [n] 本身：这是骨架类别（自然数值）的对象的命题等式，记录供下游文件沿单位子自然地传输使用。
*)

Lemma FinSet_prod_one_l (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    (@terminal_obj FinSet FinSet_Terminal) n = n.
Proof. apply Nat.mul_1_l. Qed.

Lemma FinSet_prod_one_r (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    n (@terminal_obj FinSet FinSet_Terminal) = n.
Proof. apply Nat.mul_1_r. Qed.
