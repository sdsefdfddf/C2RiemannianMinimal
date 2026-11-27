# 二维环面上的等距浸入反例

**Preprint Draft (Qi Wang, Nov 2026):** [Qi_Wang_Torus_C2_Revised.pdf](./Qi_Wang_Torus_C2_Revised.pdf)

[Lean 陈述与自然语言的逐项审核](REVIEW.md) · [定理 A](C2Riemannian/TorusCounterexample.lean) · [非存在推论](C2Riemannian/TorusImmersionCounterexample.lean) · [Lean 审计入口](Audit.lean)

```lean
import C2RiemannianMinimal

#check C2Riemannian.theorem_A
#check C2Riemannian.exists_c2_torus_metric_not_locally_c11_isometrically_immersible
#check C2Riemannian.exists_c2_torus_metric_not_c11_isometrically_immersible
#check C2Riemannian.exists_c2_torus_metric_not_c2_isometrically_immersible
#check C2Riemannian.exists_c2_torus_metric_not_isometrically_embeddable
```

给定环面点和误差上界 $\varepsilon>0$，定理 A 给出一个 $C^2$ 黎曼度量。对每个正整数 $m$，该度量在指定点附近都没有到 $\mathbb R^m$ 的弱等距浸入。同一个度量在该点附近也没有到任何有限维欧氏空间的 $C^{1,1}$ 等距浸入。这个局部障碍排除整个环面上的 $C^{1,1}$ 等距浸入，进而排除 $C^2$ 等距浸入和 $C^2$ 等距嵌入。

## 构建与复核

包使用 `lean-toolchain` 指定的 Lean 工具链及 `lake-manifest.json` 锁定的依赖。在包根目录运行以下命令，构建入口并显示定理类型与传递公理。

```sh
lake build C2RiemannianMinimal
lake env lean Audit.lean
```

定理 A 和四条非存在推论的传递公理均为 `propext`、`Classical.choice` 和 `Quot.sound`。

## 扩展结果与正则性图谱说明

在二维环面 $C^2$ 与 $C^{1,1}$ 临界反例的基础上，本仓库同步收录了实希尔伯特空间推广与其余高余维情形的 Lean 4 形式化验证包，并对闭光滑曲面高余维等距嵌入的正则性边界与文献归属作如下说明。

### 1. 实希尔伯特空间推广

* **形式化验证包：** [GitHub Release hilbert-v1.0.0](https://github.com/sdsefdfddf/C2RiemannianMinimal/releases/tag/hilbert-v1.0.0)
* **说明：** 由 `@FatFish` 在独立复核本仓库主结论与四条非存在推论的基础上提出并完成 Lean 4 形式化验证，将相关障碍机制进一步推广至实希尔伯特空间情形。

### 2. 其余高余维情形的 Lean 4 形式化核验

* **形式化验证包：** [isometric-embedding-lean-handoff (1).zip](./isometric-embedding-lean-handoff%20%281%29.zip)（对应提交 `dtq-extra-open-cases`）
* **说明：** 由 `@dtq1997` 在本仓库主结果基础上独立完成 Lean 4 形式化核验，覆盖正则性图谱中的其余高余维情形，包括 $r > 2$ 区域内的 $C^{k,1}$ （ $k \ge 2$ ）同阶端点，以及要求更高正则性（如从 $C^{k,1}$ 到 $C^{k+1}$ ）时的障碍情形。
* **文献归属说明：** 二阶以上的高阶 Lipschitz 同阶嵌入存在性 $C^{k,1}$ （ $k \ge 2$ ）已有既有数学证明，参见 Ben Andrews (2002, §5.9, pp. 190–195, Remark 5.8，取整数 $s = k + 1 > 2$ )；本仓库该部分的工作定位为在此既有理论基础上的独立机器形式化核验。

### 3. 闭光滑曲面高余维等距嵌入正则性总览

设 $g$ 为闭光滑曲面 $M$ 上正则性为 $r$ 的正定黎曼度量，考察其到有限维欧氏空间中正则性为 $s$ 的等距嵌入或浸入的存在性：

| 度量正则性 | 存在性结论与主要文献 | 临界障碍与反例情形 |
| :--- | :--- | :--- |
| $r = 0$ | 存在 $C^1$ 等距嵌入（Nash 1954; Kuiper 1955） | 无 |
| $0 < r < 2$ | 对每个严格指数 $0 < \alpha < r/2$ 存在 $C^{1,\alpha}$ 等距嵌入（Källén 1978；等号 $s = 1 + r/2$ 曾列为开放问题，参见 Källén p. 31） | 要求 $C^{1,\theta}$ （ $\theta > r/2$ ）时存在反例 |
| $r = 2$ （ $C^{1,1}$ 或 $C^2$ ） | 对每个严格次端点 $0 < \alpha < 1$ 均存在 $C^{1,\alpha}$ 等距嵌入（Källén 1978） | 本仓库新进展：存在二维环面上的 $C^2$ 度量，对任意有限维 $R^m$ 均无局部 $C^{1,1}$ 等距浸入，锁定 ( $C^{1,1}$ , $C^{1,1}$ )、( $C^2$ , $C^{1,1}$ ) 与 ( $C^2$ , $C^2$ ) 三个临界反例端点（Lean 4 已验） |
| $r > 2$ | 存在同正则性 $s = r$ 的等距嵌入：含 $C^k$ （ $k \ge 3$ ，Nash 1956）、 $C^{k,\beta}$ （ $k \ge 2$ ， $0 < \beta < 1$ ，Jacobowitz 1972; Günther 1989）及 $C^{k,1}$ （ $k \ge 2$ ，Andrews 2002, §5.9；独立 Lean 4 核验见 `@dtq1997` 验证包） | 要求更高正则性 $s > r$ 时存在反例（含从 $C^{k,1}$ 到 $C^{k+1}$ 情形） |

### 参考文献（节选）

* B. Andrews, *Notes on the isometric embedding problem and the Nash–Moser implicit function theorem*, in *Special Program on Spectral and Scattering Theory: Surveys in Analysis and Operator Theory*, Proc. Centre Math. Appl. Austral. Nat. Univ., vol. **40**, Australian National University, Canberra, 2002, 157–208 (§5.9 & Remark 5.8).
* M. Günther, *Zum Einbettungssatz von J. Nash*, Math. Nachr. **144** (1989), 165–187.
* H. Jacobowitz, *Implicit function theorems and isometric embeddings*, Ann. of Math. (2) **95** (1972), no. 2, 191–225.
* A. Källén, *Isometric embedding of a smooth compact manifold with a metric of low regularity*, Ark. Mat. **16** (1978), 29–50.
* N. H. Kuiper, *On C¹-isometric imbeddings. I, II*, Indag. Math. **17** (1955), 545–556, 683–689.
* J. Nash, *C¹ isometric imbeddings*, Ann. of Math. (2) **60** (1954), 383–396; *The imbedding problem for Riemannian manifolds*, Ann. of Math. (2) **63** (1956), no. 1, 20–63.
