# 二维环面等距浸入反例的数学审核

## 环面、切向量与度量

Lean 的 `FlatTorus` 是 `Fin 2 → AddCircle (1 : ℝ)`，即标准光滑二维环面 $\mathbb T^2=(\mathbb R/\mathbb Z)^2$。`Plane` 是 `EuclideanSpace ℝ (Fin 2)`，`Target m` 是 `EuclideanSpace ℝ (Fin m)`，分别对应带标准内积的 $\mathbb R^2$ 与 $\mathbb R^m$。记 `torusProjection` 为 $\pi:\mathbb R^2\to\mathbb T^2$。它逐坐标取模整数，是开满射。`flatPatch_openEmbedding` 给出半径为 $1/4$ 的平面开盘与其环面像之间的坐标图。`flatPatch_transition_germ` 说明坐标过渡局部是整数平移。平移的微分是恒等映射，因此切向量在各图中的分量使用同一平行标架。[环面和坐标图定义](C2Riemannian/FlatTorusMetric.lean) · [欧氏空间类型](C2Riemannian/HessianAlgebra.lean)

```lean
public structure C2TorusMetric where
  form : FlatTorus → LinearMap.BilinForm ℝ Plane
  symmetric : ∀ q X Y, form q X Y = form q Y X
  positive : ∀ q X, X ≠ 0 → 0 < form q X X
  contDiff : ∀ X Y, ContDiff ℝ 2 (fun x => form (torusProjection x) X Y)
```

| Lean 字段 | 数学条件 |
| --- | --- |
| `form q` | 为每个环面点 $q$ 给出 $(X,Y)\mapsto g_q(X,Y)$，其中 `LinearMap.BilinForm ℝ Plane` 保证两个变量各自实线性。 |
| `symmetric` | $g_q(X,Y)=g_q(Y,X)$。 |
| `positive` | 对每个 $q$ 和每个非零 $X$，$g_q(X,X)>0$。因此 $g_q$ 为切空间上的正定内积。 |
| `contDiff` | 对每对固定向量 $X,Y$，$x\mapsto g_{\pi(x)}(X,Y)$ 在整个覆盖平面上是 $C^2$。 |

在最后一项中取标准基向量 $X=e_i,Y=e_j$，便得到四个矩阵系数的 $C^2$ 正则性。反过来，对固定 $X,Y$ 的取值是这些系数乘以常数 $X_iY_j$ 后的有限和。于是 Lean 字段与“度量张量在环面坐标中为 $C^2$”等价。这里的正则性属于**输入度量** $g$。后续浸入谓词中的正则性属于**映射** $F$。[度量结构定义](C2Riemannian/TorusIsometricEmbedding.lean)

## $C^2$ 等距浸入、$C^{1,1}$ 等距浸入与 $C^2$ 等距嵌入

### 共同的等距条件

```lean
@[expose] public def C2TorusMetric.HasIsometricDifferential {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ∀ x X Y,
    let D := fderiv ℝ (F ∘ torusProjection) x
    inner ℝ (D X) (D Y) = g.form (torusProjection x) X Y
```

令 $H=F\circ\pi$。外层 `∀ x X Y` 逐点量化每个覆盖点 $x$ 和每对切向量 $X,Y\in\mathbb R^2$。在下列带正则性条件的谓词中，`fderiv ℝ H x` 是实 Fréchet 导数 $DH(x)$。由于 $\pi$ 在坐标盘内给出环面坐标，$DH(x)$ 就是 $dF_{\pi(x)}$ 在平行标架中的写法。等式精确表示
$$
\langle DH(x)X,DH(x)Y\rangle_{\mathbb R^m}
=g_{\pi(x)}(X,Y).
$$
这就是 $F^*\langle\cdot,\cdot\rangle_{\mathbb R^m}=g$。取 $Y=X\ne0$，正定性给出 $\|DH(x)X\|^2=g_{\pi(x)}(X,X)>0$，故微分单射，得到通常的浸入条件。拉回等式也给出沿曲线逐点保持速度的长度，从而保持曲线长度。[拉回等式定义](C2Riemannian/TorusIsometricEmbedding.lean)

### 两种正则性及嵌入条件

```lean
@[expose] public def C2TorusMetric.IsC2IsometricImmersion {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 2 (F ∘ torusProjection) ∧ g.HasIsometricDifferential F

@[expose] public def C2TorusMetric.IsC11IsometricImmersion {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 1 (F ∘ torusProjection) ∧
    LocallyLipschitz (fderiv ℝ (F ∘ torusProjection)) ∧ g.HasIsometricDifferential F

@[expose] public def C2TorusMetric.IsC2IsometricEmbedding {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  Topology.IsEmbedding F ∧ g.IsC2IsometricImmersion F
```

- **$C^2$ 等距浸入。** `ContDiff ℝ 2 H` 表示 $H$ 有连续的一阶和二阶实 Fréchet 导数。由于每个环面点都有上述覆盖坐标图，这等价于 $F$ 在环面图中为 $C^2$。再加上逐点拉回等式，即为通常意义的 $C^2$ 等距浸入。
- **$C^{1,1}$ 等距浸入。** 第一项要求 $H$ 为 $C^1$，第二项检验整个连续线性映射值函数 $DH$ 的局部 Lipschitz 性。具体地，对每个 $x$，存在邻域 $V_x$ 和有限常数 $L_x\ge0$，使任意 $y,z\in V_x$ 满足
  $$
  \|DH(y)-DH(z)\|_{\mathrm{op}}\le L_x\,\|y-z\|_{\mathbb R^2}.
  $$
  $V_x$ 和 $L_x$ 随 $x$ 选取。这里用 $C^{1,1}$ 表示 $C^1$ 且一阶导数局部 Lipschitz。第三项是与 $C^2$ 浸入相同的逐点拉回等式。
- **$C^2$ 等距嵌入。** 在 $C^2$ 等距浸入的基础上，`Topology.IsEmbedding F` 要求 $F$ 是到其像的同胚，像取欧氏空间的子空间拓扑。其 Lean 字段是 `IsInducing F` 和 `Function.Injective F`，分别给出源拓扑与诱导拓扑一致以及映射单射。[三个谓词源码](C2Riemannian/TorusIsometricEmbedding.lean)

### 指定点附近的 $C^{1,1}$ 等距浸入

```lean
@[expose] public def C2TorusMetric.HasLocalC11IsometricImmersion
    (g : C2TorusMetric) (o : FlatTorus) (m : ℕ) : Prop :=
  ∃ a : Plane, torusProjection a = o ∧
    ∃ U : Opens Plane, (0 : Plane) ∈ (U : Set Plane) ∧
      (U : Set Plane) ⊆ Metric.ball 0 (1 / 4) ∧
      ∃ W : Plane → Target m, ContDiffOn ℝ 1 W (U : Set Plane) ∧
        LocallyLipschitzOn (U : Set Plane) (fderiv ℝ W) ∧
        ∀ x ∈ (U : Set Plane), ∀ X Y,
          let D := fderiv ℝ W x
          inner ℝ (D X) (D Y) = g.form (torusProjection (a + x)) X Y
```

这个存在谓词要求依次找到以下对象。

1. 点 $o$ 的一个提升 $a$，即 $\pi(a)=o$。
2. 含原点的开域 $U\subseteq B_{\mathbb R^2}(0,1/4)$。$x\mapsto\pi(a+x)$ 把它嵌入环面，像是 $o$ 的一个开邻域。
3. 坐标映射 $W$。在 $U$ 上，`ContDiffOn ℝ 1 W` 要求 $C^1$ 正则性，`LocallyLipschitzOn U (fderiv ℝ W)` 要求每个 $x\in U$ 有一个相对 $U$ 的邻域，在其上 $DW$ 服从同类型的 Lipschitz 不等式。最后一项要求对每个 $x\in U$ 和任意 $X,Y$ 有
   $$
   \langle DW(x)X,DW(x)Y\rangle_{\mathbb R^m}
   =g_{\pi(a+x)}(X,Y).
   $$

Lean 用 `W : Plane → Target m` 存放坐标映射。对开集 $U$ 内的点，`fderivWithin_of_isOpen` 将域内导数识别为 `fderiv`，而 `Filter.EventuallyEq.fderiv_eq` 表明导数只取决于点附近的值。因此，数学上的候选映射可先限制到这个坐标域，再任意延拓到平面以填充函数类型。更大的环面邻域也可以缩到这样的 $U$，所以否定该谓词就是排除在 $o$ 的**任何开邻域**上的 $C^{1,1}$ 等距浸入。[局部谓词源码](C2Riemannian/TorusIsometricEmbedding.lean)

## 定理 A 的完整陈述

```lean
public theorem theorem_A (o : FlatTorus) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → ℝ, ∃ C : ℝ, C < ε ∧
      ContDiff ℝ 2 (torusCoefficient f o ∘ torusProjection) ∧
      ContDiffOn ℝ ∞ (torusCoefficient f o ∘ torusProjection) {x | torusProjection x ≠ o} ∧
      (∀ q X, X ≠ 0 → 0 < torusMetricForm f o q X X) ∧
      (∀ x, ‖torusCoefficient f o (torusProjection x)‖ ≤ C ∧
        ‖fderiv ℝ (torusCoefficient f o ∘ torusProjection) x‖ ≤ C ∧
        tensorHS (iteratedFDeriv ℝ 2 (torusCoefficient f o ∘ torusProjection) x) ≤ C) ∧
      (∀ a : Plane, torusProjection a = o →
        centeredCoefficient f o a 0 = 0 ∧ fderiv ℝ (centeredCoefficient f o a) 0 = 0 ∧
        iteratedFDeriv ℝ 2 (centeredCoefficient f o a) 0 = 0) ∧
      (∀ m : ℕ, 0 < m → ¬ HasLocalWeakTorusIsometry f o m) ∧
      (∀ (m : ℕ), 0 < m → ∀ G : FlatTorus → Target m, ¬ IsGlobalC2TorusIsometry f o G)
```

### 见证、度量与逐项条件

**自然语言陈述。** 对任意指定点 $o\in\mathbb T^2$ 和任意 $\varepsilon>0$，存在一个以平直度量为背景的正定 $C^2$ 黎曼度量 $g$。它与平直度量的 $C^2$ 距离严格小于 $\varepsilon$，在 $o$ 之外光滑，并且扰动在 $o$ 的值、一阶导数和二阶导数都为零。对每个正整数 $m$，$g$ 在 $o$ 的任何开邻域上都没有到 $\mathbb R^m$ 的局部 $W^{2,\infty}_{\mathrm{loc}}$ 弱等距浸入，整个环面上也没有到 $\mathbb R^m$ 的 $C^2$ 等距浸入。[定理 A 源码](C2Riemannian/TorusCounterexample.lean)

外层参数 `(o : FlatTorus) {ε : ℝ} (hε : 0 < ε)` 给出 $\forall o\,\forall\varepsilon>0$。接着 `∃ f : Plane → ℝ, ∃ C : ℝ` 选取辅助平面函数 $f$ 和统一的实数常数 $C$。令
$$
v(q)=\operatorname{torusCoefficient}(f,o,q),\qquad
\widetilde v=v\circ\pi,\qquad
v_a(x)=\widetilde v(a+x).
$$
`torusCoefficient` 通过周期化和中心平移得到环面系数 $v$，`centeredCoefficient f o a` 是 $v_a$。`torusMetricForm f o q X Y` 等于
$$
(1+v(q))X_0Y_0+X_1Y_1,
$$
因此 $g=(1+v)\,dx^2+dy^2$，以 $g_{\mathrm{flat}}=dx^2+dy^2$ 表示平直度量。[系数和度量公式](C2Riemannian/FlatTorusMetric.lean)

| Lean 合取项 | 逐项翻译 |
| --- | --- |
| `C < ε` | 同一个界 $C$ 严格小于输入精度 $\varepsilon$。 |
| `ContDiff ℝ 2 (torusCoefficient f o ∘ torusProjection)` | $\widetilde v$ 在整个 $\mathbb R^2$ 上为 $C^2$，因此 $g$ 在整个环面上为 $C^2$。 |
| `ContDiffOn ℝ ∞ … {x \| torusProjection x ≠ o}` | $\widetilde v$ 在 $\pi^{-1}(\mathbb T^2\setminus\{o\})$ 上为 $C^\infty$，即度量在环面上除 $o$ 之外光滑。 |
| `∀ q X, X ≠ 0 → 0 < torusMetricForm f o q X X` | 在每一点 $q$，每个非零切向量的平方长度都严格为正。 |
| `∀ x, … ≤ C ∧ … ≤ C ∧ … ≤ C` | 对同一覆盖点变量 $x$ 的全部取值，$\lvert\widetilde v(x)\rvert$、$\|D\widetilde v(x)\|_{\mathrm{op}}$ 以及 $\|D^2\widetilde v(x)\|_{\mathrm{HS}}$ 都由同一个 $C$ 控制。 |
| `∀ a : Plane, torusProjection a = o → …` | 对 $o$ 的每个提升 $a$，有 $v_a(0)=0$、$Dv_a(0)=0$ 和 $D^2v_a(0)=0$。这是扰动 $g-g_{\mathrm{flat}}$ 在 $o$ 的零二阶喷射，特别有 $g_o=(g_{\mathrm{flat}})_o$。 |
| `∀ m : ℕ, 0 < m → ¬ HasLocalWeakTorusIsometry f o m` | 对每个正目标维数，否定一个局部弱等距浸入所需的提升点、开域及弱导数场的联合存在。 |
| `∀ (m : ℕ), 0 < m → ∀ G : FlatTorus → Target m, ¬ IsGlobalC2TorusIsometry f o G` | 对每个正目标维数，以及每个从整个环面到该空间的候选映射 $G$，全局 $C^2$ 等距条件均不成立。 |

平直标架中 $g-g_{\mathrm{flat}}$ 的唯一可能非零矩阵分量是 $v$。因此表中三个上界对应的准确范数是
$$
\max\left\{\sup_x|\widetilde v(x)|,\
           \sup_x\|D\widetilde v(x)\|_{\mathrm{op}},\
           \sup_x\|D^2\widetilde v(x)\|_{\mathrm{HS}}\right\}
\ \le C<\varepsilon.
$$
`tensorHS_eq_sqrt_sum` 按二维正交标准基对二阶张量的四个有序分量取平方和再开方。对称 Hessian 的混合项因此计两次，即其范数为 $\sqrt{\widetilde v_{00}^2+2\widetilde v_{01}^2+\widetilde v_{11}^2}$。这里的 `C` 是三个估计共用的上界，取值范围是实数，其非负性已由范数界推出。前置的 $o,\varepsilon$ 可以改变见证 $f,C$。固定 $o,\varepsilon$ 后，见证位于两个 `∀ m` 之外，因此同一度量覆盖所有正目标维数和邻域。[Hilbert–Schmidt 范数定义](C2Riemannian/QuantitativeCutoff.lean)

### 局部弱条件

```lean
@[expose] public def HasLocalWeakTorusIsometry (f : Plane → ℝ) (o : FlatTorus) (m : ℕ) : Prop :=
  ∃ a : Plane, torusProjection a = o ∧
    ∃ U : Opens Plane, (0 : Plane) ∈ (U : Set Plane) ∧
      (U : Set Plane) ⊆ Metric.ball 0 (1 / 4) ∧
      ∃ w : WeakJet2 m U, w.LocallyBoundedOnCompacts ∧ w.IsometryInChart (centeredCoefficient f o a)
```

提升点 $a$ 和开域 $U$ 的意义与局部 $C^{1,1}$ 谓词相同。最后存在的 `w : WeakJet2 m U` 包含三个场和两条弱导数等式：

```lean
public structure WeakJet2 (m : ℕ) (U : Opens Plane) where
  value : Plane → Target m
  gradient : Plane → Plane →L[ℝ] Target m
  second : Plane → Plane →L[ℝ] (Plane →L[ℝ] Target m)
  weak_value : TauCeti.HasWeakFDerivOn volume U value gradient
  weak_gradient : TauCeti.HasWeakFDerivOn volume U gradient second
```

`value` 给出坐标映射 $W$，`gradient` 给出它的弱一阶导数 $P$，`second` 给出 $P$ 的弱导数，也就是 $W$ 的弱二阶导数。`weak_value` 和 `weak_gradient` 把它们联系为**同一个映射**的连续两次弱导数。按 `HasWeakFDerivOn` 的定义，这些条件以坐标域上的局部可积性和对紧支撑光滑测试函数的分部积分表达。例如，一阶关系在坐标方向 $e_i$ 上给出 $\int_U (\partial_i\varphi)W=-\int_U\varphi(Pe_i)$，二阶关系把同一条件应用于 $P$。[弱导数结构](C2Riemannian/WeakAnalysis.lean) · [弱导数定义](TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean)

```lean
@[expose] public def LocallyBoundedOnCompacts {m : ℕ} {U : Opens Plane}
    (w : WeakJet2 m U) : Prop :=
  ∀ S : Set Plane, IsCompact S → S ⊆ (U : Set Plane) →
    MemLp w.value ∞ (volume.restrict S) ∧ MemLp w.gradient ∞ (volume.restrict S) ∧
    MemLp w.second ∞ (volume.restrict S) ∧
    ∃ B : ℝ, ∀ᵐ x ∂volume.restrict S, (w.hessian x).frobenius ≤ B
```

这里 `MemLp … ∞ (volume.restrict S)` 对应在紧子集 $S$ 上本质有界。每个 $S\subseteq U$ 都可以有自己的界，分量也可以具有各自的本质界。第四项显式规定弱 Hessian 的局部 Frobenius 界。二维中每个坐标分量的范数都受二阶场的算子范数控制，四项平方求和给出 Frobenius 估计，混合弱导数通过 `second_symm_ae` 在几乎处处意义下一致。这些条件对应通常的局部 $W^{2,\infty}$ 正则性。弱场可在等价类中选代表，并在坐标域外延拓以适应 Lean 的函数类型。[局部有界定义](C2Riemannian/ClassicalC2ImmersionJet.lean) · [混合弱导数](C2Riemannian/WeakAnalysis.lean)

```lean
@[expose] public def IsometryInChart (w : WeakJet2 m U) (v : Plane → ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict (U : Set Plane),
    inner ℝ (w.gradient x ex) (w.gradient x ex) = 1 + v x ∧
    inner ℝ (w.gradient x ey) (w.gradient x ey) = 1 ∧
    inner ℝ (w.gradient x ex) (w.gradient x ey) = 0
```

在标准基 `ex`、`ey` 上，三式分别表示 $xx$、$yy$、$xy$ 分量为 $1+v_a(x)$、$1$、$0$。`∀ᵐ x ∂volume.restrict (U : Set Plane)` 表示关于 $U$ 上限制的二维 Lebesgue 测度几乎处处成立。两边的双线性型均对称，所以这三项确定几乎处处的完整拉回内积。在这些等式成立的满测集上，定理 A 的度量正定性使弱微分 $P(x)$ 单射。定理 A 否定整个存在谓词，因而 $a,U,w$ 都在排除范围内。[弱 Gram 等式](C2Riemannian/IsometryInChart.lean)

### 定理 A 的全局 $C^2$ 条件

```lean
@[expose] public def IsGlobalC2TorusIsometry {m : ℕ} (f : Plane → ℝ) (o : FlatTorus)
    (G : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 2 (G ∘ torusProjection) ∧
    ∀ a : Plane, ∀ x : Plane, x ∈ Metric.ball (0 : Plane) (1 / 4) →
      let D := fderiv ℝ (fun y => G (torusProjection (a + y))) x
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ex) = 1 + centeredCoefficient f o a x ∧
      inner ℝ (D WeakJet2.ey) (D WeakJet2.ey) = 1 ∧
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ey) = 0
```

这里对所有覆盖平面中心 $a$ 及盘内点 $x$ 逐点检验经典导数的三个 Gram 分量。中心 $a$ 可以是任意平面点。由平移导数恒等式 `fderiv_comp_add_left`，`D` 就是 $D(G\circ\pi)(a+x)$。第一个右端为 $1+v(\pi(a+x))$，另两项为 $1$ 和 $0$，所以完整拉回等式蕴含这三项。反过来，对任意覆盖点 $z$ 取 $a=z$、$x=0$，得到该点三项 Gram 条件，再由双线性和对称性恢复所有 $(X,Y)$ 的拉回等式。因此，对 A 给出的对角度量，这一旧谓词与 `g.IsC2IsometricImmersion G` 的几何含义一致。其正则性条件都是 `ContDiff ℝ 2 (G ∘ torusProjection)`，等距条件都是逐点成立。[定理 A 所用的全局谓词](C2Riemannian/TorusCounterexample.lean) · [一般度量的浸入谓词](C2Riemannian/TorusIsometricEmbedding.lean)

## 四条非存在推论的量词

```lean
public theorem exists_c2_torus_metric_not_locally_c11_isometrically_immersible (o : FlatTorus) :
    ∃ g : C2TorusMetric, ¬ ∃ m : ℕ, g.HasLocalC11IsometricImmersion o m

public theorem exists_c2_torus_metric_not_c11_isometrically_immersible :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC11IsometricImmersion F

public theorem exists_c2_torus_metric_not_c2_isometrically_immersible :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC2IsometricImmersion F

public theorem exists_c2_torus_metric_not_isometrically_embeddable :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC2IsometricEmbedding F
```

| Lean 声明 | 自然语言与量词 |
| --- | --- |
| `exists_c2_torus_metric_not_locally_c11_isometrically_immersible (o : FlatTorus)` | 对每个指定点 $o$，存在一个 $C^2$ 度量 $g$，对每个自然数 $m$ 都没有 $o$ 附近到 $\mathbb R^m$ 的 $C^{1,1}$ 等距浸入。这里 $a,U,W$ 的存在性已写入局部谓词。量词顺序为 $\forall o\,\exists g\,\forall m$，最内层否定 `g.HasLocalC11IsometricImmersion o m`。 |
| `exists_c2_torus_metric_not_c11_isometrically_immersible` | 存在一个 $C^2$ 度量 $g$，对每个 $m$ 和每个定义在整个环面上的 $F\colon\mathbb T^2\to\mathbb R^m$，$F$ 都不能成为 $g$ 的 $C^{1,1}$ 等距浸入。 |
| `exists_c2_torus_metric_not_c2_isometrically_immersible` | 存在一个 $C^2$ 度量 $g$，对每个 $m,F$，$F$ 都不能成为 $g$ 的 $C^2$ 等距浸入。 |
| `exists_c2_torus_metric_not_isometrically_embeddable` | 存在一个 $C^2$ 度量 $g$，对每个 $m,F$，$F$ 都不能成为 $g$ 的 $C^2$ 等距嵌入。 |

三个全局结论都使用 $\exists g\,\neg\exists(m,F)$，即 $\exists g\,\forall m\,\forall F\,\neg(\cdots)$。度量先于所有目标维数及映射选出。这里的 `m : ℕ` 包含零维。定理 A 本身的排除量词带有 `0 < m`。新增的局部推论另行处理 $m=0$，因为 $\mathbb R^0$ 中一切导数分量为零，与 `yy` Gram 分量等于 $1$ 矛盾。[四条推论源码](C2Riemannian/TorusImmersionCounterexample.lean)

## 推导中保持的数学对象与条件

1. **定理 A 到局部 $C^{1,1}$ 非存在。** 代码在给定点 $o$ 对 A 取 $\varepsilon=1$，把同一个 `torusMetricForm f o` 包成 `C2TorusMetric`。对于局部 $C^{1,1}$ 候选，`weakJet2_of_contDiffOn_locallyLipschitz` 保持原映射 $W$ 和经典一阶导数 $DW$，把 $DW$ 的几乎处处导数识别为其弱导数。对任意紧子集，局部 Lipschitz 条件提供紧邻域上的 Lipschitz 常数 $L$，由此得到二阶导数算子范数界 $L$ 和 Hessian Frobenius 界 $2L$。`weakJet2_of_contDiffOn_locallyLipschitz_locallyBounded` 就是这一局部界的 Lean 声明。原候选的逐点拉回等式取标准基后给出 A 所需的几乎处处 Gram 等式。正维情况由此应用 A 的局部弱非存在项。[弱导数构造](C2Riemannian/ClassicalToWeakJet.lean) · [紧集界](C2Riemannian/ClassicalC11ImmersionJet.lean)
2. **局部到全局。** `IsC11IsometricImmersion.hasLocal` 对全局候选 $F$ 构造同一个映射的中心坐标限制 $x\mapsto F(\pi(a+x))$。平移保持一阶导数的局部 Lipschitz 性与逐点拉回等式。全局非存在推论取局部非存在声明在 $o=0$ 得到的度量。[中心坐标限制](C2Riemannian/TorusIsometricEmbedding.lean)
3. **全局 $C^{1,1}$ 到全局 $C^2$ 非存在。** `IsC2IsometricImmersion.isC11IsometricImmersion` 用 `fderiv_right` 得到 $D(F\circ\pi)$ 为 $C^1$，再用 `ContDiff.locallyLipschitz` 得到它的局部 Lipschitz 性。这一步只改变对同一个映射的正则性证据，度量 $g$ 和拉回等式仍用原来的值。因此 $C^2$ 候选会给出已被排除的 $C^{1,1}$ 候选。[正则性蕴含](C2Riemannian/TorusIsometricEmbedding.lean)
4. **$C^2$ 浸入到 $C^2$ 嵌入非存在。** 嵌入谓词的第二个合取项 `hF.2` 是 $C^2$ 等距浸入。将其交给前一条非存在推论，即排除同一度量的 $C^2$ 等距嵌入。[推导链](C2Riemannian/TorusImmersionCounterexample.lean)

对同一局部正定度量，弱与 $C^{1,1}$ 的对照还可以从弱代表元方向核验。`classical_isometry_representative` 从局部本质有界的弱场得到 $C^1$ 代表和局部 Lipschitz 的经典导数，它与原弱梯度几乎处处相等。`gram_eq_of_continuous_representative` 通过两边连续，把这个代表的几乎处处 Gram 等式提升为逐点等式。公开的非存在推论实际使用第 1 步的方向，即把一个经典候选转换为 A 所排除的弱候选。[经典代表元](C2Riemannian/ChartCurvature.lean) · [逐点 Gram 等式](C2Riemannian/IsometryInChart.lean)

## 定理 A 中局部障碍的数学来源

由弱 Gram 等式可推出标量相容方程
$$
q(D^2W)=-\tfrac12(v_a)_{yy},\qquad
q(D^2W)=\langle W_{xx},W_{yy}\rangle-\|W_{xy}\|^2.
$$
其符号与因子来自分布恒等式
$$
\partial_{yy}|W_x|^2+\partial_{xx}|W_y|^2
-2\partial_{xy}\langle W_x,W_y\rangle=-2q(D^2W).
$$
代入三项 Gram 等式，左端成为 $(v_a)_{yy}$。对向量值 $W$，右端的 $q$ 是各标量分量的二维 Hessian 行列式之和。应用于反证的是从等距条件得到标量方程的必要性。[相容方程](C2Riemannian/ChartCurvature.lean) · [标量行列式恒等式](https://msp.org/apde/2017/10-3/apde-v10-n3-p06-p.pdf#page=3)

`UniversalTorusInputs` 先为每个 $n$ 选出一个光滑紧支撑扰动，在单位盘排除目标维数 $n+1$、Hessian 界 $n+1$ 的标量方程解。选叶用实际参数树的线性源能量矛盾。把这一列扰动拼接进趋近 $o$ 的互不相交小盘后，任意候选弱浸入的有限目标维数 $m$ 和紧邻域内 Hessian 界 $K$ 都可以用足够大的 $n$ 控制。小盘缩放回单位盘并消去振幅 $\delta_n=\delta_0/(n+1)$ 后，Hessian 界变为 $K/\sqrt{\delta_n}$。充分大的 $n$ 使它至多为 $n+1$，并允许从 $\mathbb R^m$ 补零到 $\mathbb R^{n+1}$。这样得到已经排除的解。扰动列在假设候选浸入之前选定，说明这个障碍为何能够使用同一个度量覆盖不同维数与不同局部二阶界。[线性选叶](C2Riemannian/UniversalTorusInputs.lean) · [小盘拼接](C2Riemannian/GluedTorusProfile.lean) · [缩放反证](C2Riemannian/PlanarCounterexampleA.lean)

## $C^2$ 端点问题的文献出处

1. **John Nash，1956。** *The Imbedding Problem for Riemannian Manifolds*，*Annals of Mathematics* 63(1)，20–63。开篇第 21 页的 Remarks 明确提出应将 $C^2$ 情形纳入，并指出需要新的估计。第 59 页定理 2 给出紧致情形的正向嵌入定理，对输入度量和嵌入都取同一个 $k\ge3$。[刊本 DOI](https://doi.org/10.2307/1969989) · [原版第 21 页](https://mccuan.math.gatech.edu/courses/6455/nash55.pdf#page=3) · [原版定理 2](https://mccuan.math.gatech.edu/courses/6455/nash55.pdf#page=41)
2. **Misha Gromov，2017。** *Geometric, Algebraic, and Analytic Descendants of Nash Isometric Embedding Theorems*，*Bulletin of the American Mathematical Society* 54(2)，173–245。作者稿 §1.2 猜想 9 讨论给定较大有限目标维数中的局部 $C^2$ 等距浸入，正文以光滑黎曼流形为对象，并在括号中提出 $C^2$ 正则度量的扩展。定理 A 在二维排除了这个扩展的局部结论。光滑度量及猜想所给的维数范围各有其原文假设。[刊本 DOI](https://doi.org/10.1090/bull/1551) · [作者稿 §1.2](https://cims.nyu.edu/~gromov/probability%202022-23/NY2023/nash-Dec-2015.pdf#page=6)
3. **Camillo De Lellis，2019。** *The Masterpieces of John Forbes Nash Jr.*，收入 *The Abel Prize 2013–2017*，391–499，§3.1，第 425 页。此处明确把 $C^2$ 度量的 $C^2$ 等距嵌入列为当时的开放端点，紧接着 Jacobowitz 对 $C^{k,\beta}$、$k+\beta>2$ 的同阶嵌入结果。将这个普遍存在问题限制到二维闭曲面，就得到本包嵌入非存在定理所反驳的命题。[出版章节](https://doi.org/10.1007/978-3-319-99028-6_19) · [作者稿对应段落](https://arxiv.org/pdf/1606.02551#page=39) · [Jacobowitz 原论文](https://annals.math.princeton.edu/1971/95-2/p01)
4. **Stefano Nardulli 与 Reinaldo Resende，2026。** *Interior regularity of area minimizing currents within a $C^{2,\alpha}$-submanifold*，*Transactions of the American Mathematical Society* 379(2)，1023–1057。作者稿 §1 的 Remark 1.3 在讨论把内蕴正则性结果转到欧氏空间时，再次记载 $C^2$ 情形的 Nash 等距嵌入是开放问题。[刊本 DOI](https://doi.org/10.1090/tran/9502) · [作者稿 Remark 1.3](https://arxiv.org/pdf/2404.17407v2#page=2)

这些文献记录了一般 $C^2$ 端点问题。本包的环面构造与定理 A 来自研究稿《二维环面上纯 $C^2$ 度量的局部等距浸入反例》。

## 源码范围与复核入口

`import C2RiemannianMinimal` 提供定理 A 和上述四条非存在推论。源码按这些声明的传递导入提取，省去命题 A.1 的附录验证以及定理 B、C 的终端证明。定理 A 使用线性源选叶，实际参数树带有构造共用的状态与估计，其中包括四阶势字段。随附的 Tau Ceti Sobolev 源码来自固定提交 `040e460d13a512f97280ca701265d75f71114490`，许可证见 `TauCeti/LICENSE`。[Tau Ceti 固定源码](https://github.com/TauCetiProject/TauCeti/tree/040e460d13a512f97280ca701265d75f71114490)

[Audit.lean](Audit.lean) 用 `#check` 显示完整类型，用 `#print` 显示本审核使用的度量、浸入及弱等距谓词定义，用 `#print axioms` 检查五条证明的传递公理。[README](README.md) 给出构建与复核命令。
