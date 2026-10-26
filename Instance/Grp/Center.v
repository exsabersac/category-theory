Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The center of a group is not functorial

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §I.3
   (printed pp. 14–15): the remark that the center Z(G) supports no
   extension to a functor, and Exercise 4's sharpening
   [maclane:I.3:remark1, maclane:I.3:ex4]: there is NO functor
   T : Grp ⟶ Ab whose object function is G ↦ Z(G) — the quantification
   is over ALL functors with that object function, arbitrary arrow
   function included.
   Wikipedia: https://en.wikipedia.org/wiki/Center_(group_theory)

   THE CENTER ITSELF ([IsCentral], [CenterGrp], [CenterAb]): the
   elements commuting with everything form a subgroup — closure under
   unit, multiplication, and inversion are the classical one-line
   chains — and that subgroup is abelian BY CONSTRUCTION (centrality
   of one factor is exactly commutation with the other), so the
   center lands in [AbObject] and G ↦ Z(G) is a bona fide object
   function Grp → Ab.  What it is not is functorial.

   THE COUNTEREXAMPLE is Mac Lane's retract of symmetric groups.  Two
   presentations of S₃ are in tree: Instance/Grp/Epi.v's [GrpSym3]
   (permutations of a three-element setoid, where [grp_two_sym3]
   includes ℤ/2 for that file's non-normal-image counterexample) and
   Instance/Grp/TwoFunctors.v's semidirect [S3] on rot × bool.  The
   SEMIDIRECT presentation carries the sign character definitionally
   — the bool component of [s3_mul] is [xorb] — so it is the one
   used here: [s3_sign : S3 ⟶ ℤ/2] is a homomorphism by projection,
   [grp_two_s3 : ℤ/2 ⟶ S3] includes the rotation-free elements — a
   split mono, [sign_retract] computing r ∘ i ≈ id on the two
   elements.  ℤ/2 itself is Epi.v's [GrpTwo]; no permutation model of
   S₂ is built, ℤ/2 BEING S₂ (the unique group of order two), and the
   two S₃ presentations are not related by an in-tree isomorphism —
   each serves its own file.

   UNIVERSE SCOPE, disclosed.  TwoFunctors.v's [S3] pins its carrier
   universe at Set, so [no_center_functor] as stated quantifies over
   functors on Grp AT CARRIER UNIVERSE Set — precisely the hazard
   Epi.v documents (its [GrpTwo] and three-letter setoid are built on
   [poly_unit] to avoid pinning).  The argument itself is
   universe-indifferent; a polymorphic restatement awaits either a
   [poly_unit]-based semidirect S₃ or a sign character on [GrpSym3].

   THE COMPUTATIONS: [GrpTwo_abelian] makes every element of ℤ/2
   central, giving [Center_GrpTwo_iso : CenterGrp GrpTwo ≅ GrpTwo]
   in Grp — Z(S₂) is the whole two-element group — while
   [S3_center_trivial] shows by six-way case analysis that only the
   identity of S₃ is central — the proof spends only the two
   generators — so Z(S₃) is trivial, and [central_not_preserved]
   records Mac Lane's REMARK proper: the inclusion carries ℤ/2's
   central nonidentity to the non-central reflection, so
   homomorphisms need not preserve centrality.

   THE NO-FUNCTOR THEOREM ([no_center_functor]): suppose T : Grp ⟶ Ab
   with fobj T G = CenterAb G for every G (strict equality of
   objects, the honest reading of “has G ↦ Z(G) as its object
   function”).  Functoriality sends the retract
   sgn ∘ inc ≈ id : S₂ → S₃ → S₂ to a factorization of the identity
   of Z(S₂) through Z(S₃).  Every element of Z(S₃) is the unit
   ([S3_center_trivial]), homomorphisms preserve units, so every
   element of Z(S₂) is the unit — but Z(S₂) contains the nontrivial
   element of ℤ/2, and in ℤ/2's setoid the two elements are distinct
   constructors.  Contradiction, for an ARBITRARY arrow function.
   The hypothesis is STRICT equality of objects — the literal reading
   of “has G ↦ Z(G) as its object function”; a functor agreeing with
   the center only up to isomorphism escapes this statement, and the
   up-to-iso variant is left unstated rather than claimed. 

   --------
   * * 一个群的中心不是函子性的

   Mac Lane，《从事数学工作的数学家的范畴论》，第2版，§I.3
   （印刷页 14–15）：关于中心 Z(G) 不支持扩展为函子的评论，以及练习 4 的加强版
   [maclane:I.3:remark1, maclane:I.3:ex4]：不存在函子
   T : Grp ⟶ Ab，其对象函数为 G ↦ Z(G) — 该量化涵盖了所有具有该对象函数的函子，包括任意箭头函数。
   维基百科:  https://en.wikipedia.org/wiki/Center_(group_theory)中心本身（[IsCentral]，[CenterGrp]，[CenterAb]）：与所有元素交换的元素形成一个子群——在单位元、乘法和取逆下都是封闭的，这是经典的一行链——并且该子群按构造是阿贝尔群（一个因子的中心性恰好是与另一个因子的交换性），因此中心落在 [AbObject] 中，并且 G ↦ Z(G) 是一个真正的对象函数 Grp → Ab。它不是函子。反例是 Mac Lane 对对称群的收缩。S₃ 的两个表示在树中：Instance/Grp/Epi.v 中的 [GrpSym3]（一个三元素集的置换，其中 [grp_two_sym3] 包含 ℤ/2 用于该文件的非正规像反例）以及 Instance/Grp/TwoFunctors.v 中的半直积 [S3] 在 rot × bool 上。半直积表示在定义上携带符号特征 —— [s3_mul] 的 bool 分量是 [xorb] —— 因此这里使用它：[s3_sign : S3 ⟶ ℤ/2] 是通过投影的同态，[grp_two_s3 : ℤ/2 ⟶ S3] 包含无旋转元素 —— 一个分裂单射，[sign_retract] 在两个元素上计算 r ∘ i ≈ id。ℤ/2 本身就是 Epi.v 的 [GrpTwo]；没有构建 S₂ 的排列模型，ℤ/2 就是 S₂（唯一的二阶群），而且两个 S₃ 表示之间没有通过树内同构关联——每个表示各自独立。 

   宇宙范围，已公开。TwoFunctors.v 的 [S3] 将其承载宇宙固定在 Set，因此 [no_center_functor] 所述的量化范围是对承载宇宙 Set 上 Grp 的函子——正是 Epi.v 中记录的风险（其 [GrpTwo] 和三个字母的同构集建立在 [poly_unit] 上以避免固定）。论证本身与宇宙无关；一个多态的重述等待要么是基于 [poly_unit] 的半直积 S₃，要么是 [GrpSym3] 上的符号特征。计算：[GrpTwo_abelian] 使 ℤ/2 的每个元素都是中心元素，从而在群中得到 [Center_GrpTwo_iso : CenterGrp GrpTwo ≅ GrpTwo] — Z(S₂) 是整个两元素群 — 而 [S3_center_trivial] 通过六种情况分析表明，只有 S₃ 的单位元是中心元素 — 证明只用了两个生成元 — 因此 Z(S₃) 是平凡的，[central_not_preserved] 记录了 Mac Lane 的正式备注：包含映射将 ℤ/2 的非单位中心元素映射到非中心反射元素，因此同态不必保持中心性。非函子定理 ([no_center_functor])：假设 T : Grp ⟶ Ab，且对每个群 G 都有 fobj T G = CenterAb G（对象严格相等，这是“其对象函数将 G 映射为 Z(G)”的字面意思）。函子性将收缩映射 sgn ∘ inc ≈ id : S₂ → S₃ → S₂ 发送为通过 Z(S₃) 的 Z(S₂) 恒等映射的分解。Z(S₃) 的每个元素都是单位元（[S3_center_trivial]），同态保持单位元，因此 Z(S₂) 的每个元素都是单位元——但 Z(S₂) 包含 ℤ/2 的非平凡元素，并且在 ℤ/2 的集合化体中，这两个元素是不同的构造器。矛盾，对于任意箭头函数成立。该假设是对象的严格相等 — 对“具有 G ↦ Z(G) 作为其对象函数”的字面解读；一个仅在同构意义下与中心一致的函子不在此声明之内，而同构意义下的变体被省略而非声称。
*)

(* * ** Central elements, and the center as an abelian group / * ** 中心元素，以及作为阿贝尔群的中心 *)

Definition IsCentral (G : GrpObject) (z : carrier G) : Type :=
  ∀ g : carrier G, grp_mul G z g ≈ grp_mul G g z.

Lemma central_unit (G : GrpObject) : IsCentral G (grp_unit G).
Proof.
  intro g.
  rewrite grp_mul_unit_l, grp_mul_unit_r.
  reflexivity.
Qed.

Lemma central_mul (G : GrpObject) (z w : carrier G) :
  IsCentral G z → IsCentral G w → IsCentral G (grp_mul G z w).
Proof.
  intros Hz Hw g.
  rewrite grp_mul_assoc.
  rewrite (Hw g).
  rewrite <- grp_mul_assoc.
  rewrite (Hz g).
  rewrite grp_mul_assoc.
  reflexivity.
Qed.

Lemma central_inv (G : GrpObject) (z : carrier G) :
  IsCentral G z → IsCentral G (grp_inv G z).
Proof.
  intros Hz g.
  rewrite <- (grp_mul_unit_r G (grp_mul G (grp_inv G z) g)).
  rewrite <- (grp_mul_inv_r G z).
  rewrite <- grp_mul_assoc.
  rewrite (grp_mul_assoc G (grp_inv G z) g z).
  rewrite <- (Hz g).
  rewrite <- (grp_mul_assoc G (grp_inv G z) z g).
  rewrite grp_mul_inv_l, grp_mul_unit_l.
  reflexivity.
Qed.

(*
 The carrier of the center: elements paired with their centrality
 witness, compared on the element alone (the witness is
 proof-irrelevant for the setoid).  Pairs are built with explicit
 [existT] throughout — the 8.19/8.20-safe form. 

 --------
 中心的承载者：与其中心性配对的元素，仅在元素上进行比较（见证对于集合同构是无关证明的）。配对全过程使用显式的 [existT] — 8.19/8.20 安全形式。
*)
Definition center_carrier (G : GrpObject) : Type :=
  { z : carrier G & IsCentral G z }.

Definition mk_central (G : GrpObject) (z : carrier G)
  (Hz : IsCentral G z) : center_carrier G :=
  existT (fun z : carrier G => IsCentral G z) z Hz.

Program Definition center_setoid (G : GrpObject) : SetoidObject := {|
  carrier := center_carrier G;
  is_setoid := {| equiv := fun a b => `1 a ≈ `1 b |}
|}.
Next Obligation.
  intro G; equivalence.
Qed.

Program Definition CenterGrp (G : GrpObject) : GrpObject := {|
  grp_setoid := center_setoid G;
  grp_unit := mk_central G (grp_unit G) (central_unit G);
  grp_mul := fun a b =>
    mk_central G (grp_mul G (`1 a) (`1 b))
      (central_mul G (`1 a) (`1 b) (`2 a) (`2 b));
  grp_inv := fun a =>
    mk_central G (grp_inv G (`1 a)) (central_inv G (`1 a) (`2 a));
  (*
 The centre's `≈` compares first projections in [G], so it is
 propositional exactly when [G]'s own `≈` is. 

 --------
 该中心的 `≈` 比较 [G] 中的首个投影，所以当 [G] 自身的 `≈` 是命题性时，它也是命题性。
*)
  grp_prop :=
    sigma_first_PropEquiv (is_setoid (center_setoid G))
      (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *.
  now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

(*
 The center is abelian by construction: commutation of two central
 elements is the first one's centrality at the second. 

 --------
 该中心是通过构造得到的阿贝尔群：两个中心元素的交换是第一个元素在第二个元素处的中心性。
*)
Lemma CenterGrp_abelian (G : GrpObject) (a b : carrier (CenterGrp G)) :
  grp_mul (CenterGrp G) a b ≈ grp_mul (CenterGrp G) b a.
Proof. exact (`2 a (`1 b)). Qed.

(*
 ...and therefore an object of Ab: G ↦ Z(G) really is an object
 function Grp → Ab.

 Since the PR “algebraic carriers are sets” (2026-09-17) an [AbObject]
 carries [cmon_prop], and the centre's carrier setoid compares first
 projections in [G] -- so it is propositional exactly when [G]'s own `≈`
 is.  An intermediate revision of this file (phase P2 of that PR) took the
 witness [PG] as an explicit argument, because [GrpObject] did not yet carry
 [grp_prop]; phase P3 added the field [grp_prop] and the argument is gone.
 The signature is the one it had before the PR. 

 --------
 ...因此，一个对象 Ab: G ↦ Z(G) 确实是一个对象函数 Grp → Ab。

 鉴于 PR “代数载体是集合”（2026-09-17），一个 [AbObject] 承载 [cmon_prop]，并且中心的载体集合类比较 [G] 中的第一个投影——所以当 [G] 自身的 `≈` 是命题时它恰好也是命题。该文件的一个中间修订版（该 PR 的 P2 阶段）将见证 [PG] 作为显式参数，因为 [GrpObject] 当时尚未承载 [grp_prop]；P3 阶段增加了字段 [grp_prop]，因此参数已消失。其签名是该 PR 之前的签名。
*)
Program Definition CenterAb (G : GrpObject) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := center_setoid G;
    cmon_zero := mk_central G (grp_unit G) (central_unit G);
    cmon_plus := fun a b =>
      mk_central G (grp_mul G (`1 a) (`1 b))
        (central_mul G (`1 a) (`1 b) (`2 a) (`2 b));
    cmon_prop :=
      sigma_first_PropEquiv (is_setoid (center_setoid G))
        (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
  |};
  ab_neg := fun a =>
    mk_central G (grp_inv G (`1 a)) (central_inv G (`1 a) (`2 a))
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *.
  now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a b; simpl; exact (`2 a (`1 b)). Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation.
  intros G a a' Ha; simpl in *.
  now rewrite Ha.
Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

(* The center includes into the group. / 中心包括在该组中。 *)
Program Definition Center_incl (G : GrpObject) :
  CenterGrp G ~{Grp}~> G := {|
  grp_map := {| morphism := fun a => `1 a |}
|}.
Next Obligation. intros G a b H; exact H. Qed.
Next Obligation. intros G; simpl; reflexivity. Qed.
Next Obligation. intros G a b; simpl; reflexivity. Qed.

(** ** Z(S₂) is all of S₂ / ** Z(S₂) 是 S₂ 的全部 *)

Lemma GrpTwo_abelian (a b : carrier GrpTwo) :
  grp_mul GrpTwo a b ≈ grp_mul GrpTwo b a.
Proof.
  destruct a as [[]|[]], b as [[]|[]]; exact ttt.
Qed.

Program Definition Center_GrpTwo_iso : CenterGrp GrpTwo ≅[Grp] GrpTwo := {|
  to := Center_incl GrpTwo;
  from := {| grp_map := {| morphism := fun x =>
    mk_central GrpTwo x (fun g => GrpTwo_abelian x g) |} |}
|}.
Next Obligation. intros a b H; exact H. Qed.
Next Obligation. simpl; exact ttt. Qed.
Next Obligation. intros a b; simpl; destruct a as [[]|[]], b as [[]|[]]; exact ttt. Qed.
Next Obligation. intros a; simpl; destruct a as [[]|[]]; exact ttt. Qed.
Next Obligation.
  intros a; simpl; destruct a as [z Hz]; simpl;
    destruct z as [[]|[]]; exact ttt.
Qed.

(** ** Z(S₃) is trivial / ** Z(S₃) 是平凡的 *)

(*
 Only the identity commutes with both generators: case analysis over
 the six elements, testing centrality at the rotation r = (rot1,
 false) and the reflection s = (rot0, true). 

 --------
 只有单位元与两个生成元交换：对六个元素进行情况分析，在旋转 r = (rot1, false) 和反射 s = (rot0, true) 上测试中心性。
*)
Lemma S3_center_trivial (z : carrier S3) :
  IsCentral S3 z → z = s3_unit.
Proof.
  intros Hz.
  destruct z as [[| |] [|]]; try reflexivity.
  all: try (pose proof (Hz S3_r) as E; vm_compute in E; discriminate E).
  all: pose proof (Hz S3_s) as E; vm_compute in E; discriminate E.
Qed.

(** ** The sign retract S₂ → S₃ → S₂ / ** 标志缩回 S₂ → S₃ → S₂ *)

(* ℤ/2 includes as the rotation-free permutations... / ℤ/2 包含作为无旋转置换... *)
Program Definition grp_two_s3 : GrpTwo ~{Grp}~> S3 := {|
  grp_map := {| morphism := fun x : carrier GrpTwo =>
    ((rot0, if x then false else true) : carrier S3) |}
|}.
Next Obligation.
  intros a b H; destruct a as [[]|[]], b as [[]|[]];
    (reflexivity + contradiction).
Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation.
  intros a b; destruct a as [[]|[]], b as [[]|[]]; reflexivity.
Qed.

(* ...and the sign character projects back. / ...并且符号字符向后投射。 *)
Program Definition s3_sign : S3 ~{Grp}~> GrpTwo := {|
  grp_map := {| morphism := fun p : carrier S3 =>
    if snd p then grp_two_one else grp_two_zero |}
|}.
Next Obligation. simpl; exact ttt. Qed.
Next Obligation.
  intros a b; destruct a as [ra [|]], b as [rb [|]]; simpl; exact ttt.
Qed.

(* The retract law: sign after inclusion is the identity of ℤ/2. / 收缩律：包含后的符号是 ℤ/2 的恒等元素。 *)
Lemma sign_retract :
  s3_sign ∘[Grp] grp_two_s3 ≈ @id Grp GrpTwo.
Proof.
  intros x; destruct x as [[]|[]]; exact ttt.
Qed.

(* Mac Lane's remark, before the exercise: a homomorphism need not carry central elements to central elements. The inclusion sends ℤ/2's central nonidentity to the reflection s, which S₃'s trivial center excludes. / Mac Lane 在练习前的评论：同态不必将中心元素映射到中心元素。包含映射将 ℤ/2 的中心非单位元素映射到反射 s，而 S₃ 的平凡中心不包括它。 *)
Lemma central_not_preserved :
  IsCentral GrpTwo grp_two_one *
  (IsCentral S3 (grp_map grp_two_s3 grp_two_one) → False).
Proof.
  split.
  - intro g; apply GrpTwo_abelian.
  - intro Hz.
    pose proof (S3_center_trivial _ Hz) as E.
    vm_compute in E; discriminate E.
Qed.

(** ** The no-functor theorem / ** 无函子定理 *)

(*
 An intermediate revision of this theorem (phase P2 of the PR “algebraic
 carriers are sets”, 2026-09-17) carried an extra hypothesis
 [PG : ∀ G : GrpObject, PropEquiv (is_setoid (grp_setoid G))], because
 [CenterAb] then needed the witness and [GrpObject] did not yet supply it.
 Phase P3 added the field [grp_prop], so the hypothesis is gone and the
 statement is the one it had before the PR: it quantifies over ALL functors
 [T : Grp ⟶ Ab] with the centre as object function. 

 --------
 这个定理的一个中间修订（PR“代数载体是集合”的阶段 P2，2026-09-17）包含了一个额外的假设 [PG : ∀ G : GrpObject, PropEquiv (is_setoid (grp_setoid G))]，因为 [CenterAb] 那时需要见证，而 [GrpObject] 还没有提供它。阶段 P3 添加了域 [grp_prop]，因此假设消失了，陈述回到了 PR 之前的状态：它对所有以中心作为对象函数的函子 [T : Grp ⟶ Ab] 进行量化。
*)
Theorem no_center_functor (T : Grp ⟶ Ab)
  (HT : ∀ G : GrpObject, fobj[T] G = CenterAb G) : False.
Proof.
  (* The retract factors the identity of T S₂ through T S₃. / 收缩通过 T S₃ 将 T S₂ 的同一性分解。 *)
  assert (Hrt : ∀ x : carrier (fobj[T] GrpTwo),
             cmon_map (fmap[T] s3_sign) (cmon_map (fmap[T] grp_two_s3) x)
               ≈ x).
  { intro x.
    pose proof (@fmap_comp _ _ T GrpTwo S3 GrpTwo s3_sign grp_two_s3)
      as Hc.
    pose proof (@fmap_respects _ _ T GrpTwo GrpTwo
                  (s3_sign ∘[Grp] grp_two_s3) (@id Grp GrpTwo)
                  sign_retract) as Hr.
    pose proof (@fmap_id _ _ T GrpTwo) as Hi.
    specialize (Hc x); specialize (Hr x); specialize (Hi x).
    simpl in Hc, Hr, Hi.
    now rewrite <- Hc, Hr, Hi. }
  (* Every element of T S₃ is the unit, since Z(S₃) is trivial. / T S₃ 的每个元素都是单位元，因为 Z(S₃) 是平凡的。 *)
  assert (Hall : ∀ w : carrier (fobj[T] S3),
             w ≈ cmon_zero (fobj[T] S3)).
  { rewrite (HT S3).
    intros [z Hz]; simpl.
    now rewrite (S3_center_trivial z Hz). }
  (* Hence every element of T S₂ is the unit... / 因此 T S₂ 的每个元素都是单位... *)
  assert (Hcollapse : ∀ x : carrier (fobj[T] GrpTwo),
             x ≈ cmon_zero (fobj[T] GrpTwo)).
  { intro x.
    rewrite <- (Hrt x).
    rewrite (Hall (cmon_map (fmap[T] grp_two_s3) x)).
    apply (cmon_map_zero (fmap[T] s3_sign)). }
  (* ...but Z(S₂) contains the nontrivial element of ℤ/2. / ...但是 Z(S₂) 包含 ℤ/2 的非平凡元素。 *)
  generalize Hcollapse.
  rewrite (HT GrpTwo).
  intro Hc2.
  exact (Hc2 (mk_central GrpTwo grp_two_one
                (fun g => GrpTwo_abelian grp_two_one g))).
Qed.
