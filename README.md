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
## 扩展结果与完整正则性图谱

在二维环面 $C^2 / C^{1,1}$ 临界反例的基础上，本仓库同步收录了高余维剩余开放情形与实希尔伯特空间推广的 Lean 4 形式化验证包，至此闭光滑曲面高余维等距嵌入的完整正则性图谱已全部封顶。

### 1. 剩余高余维开放情形（含 $C^{k,1},\ k \ge 2$）

* **形式化验证包：** [isometric-embedding-lean-handoff (1).zip](<./isometric-embedding-lean-handoff (1).zip>)（对应提交 `dtq-extra-open-cases`）
* **核验与说明：** 由 `@dtq1997` 在本仓库主结果基础上独立完成 Lean 4 形式化核验，补齐了 $r > 2$ 区域内的剩余开放端点（包括 $C^{k,1},\ k \ge 2$ 度量存在同正则性等距嵌入，以及要求更高正则性如 $C^{k,1} \to C^{k+1}$ 时存在反例等情形）。

### 2. 实希尔伯特空间推广

* **形式化验证包：** [GitHub Release `hilbert-v1.0.0`](https://github.com/sdsefdfddf/C2RiemannianMinimal/releases/tag/hilbert-v1.0.0)
* **核验与说明：** 由 `@FatFish` 在交流与独立复核主结论过程中提出并完成 Lean 4 形式化验证，将相关障碍机制进一步推广至实希尔伯特空间情形。

### 3. 闭光滑曲面高余维等距嵌入正则性总览

设 $g$ 为闭光滑曲面 $M$ 上正则性为 $r$ 的正定黎曼度量，考察其到有限维欧氏空间中正则性为 $s$ 的等距嵌入/浸入的存在性，全部情形现已彻底定论：

| 度量正则性 $r$ | 可达的最优嵌入正则性 | 临界障碍与反例情形 |
| :--- | :--- | :--- |
| $r = 0$ | 存在 $C^1$ 等距嵌入 | — |
| $0 < r < 2$ | 存在 $C^{1,\,r/2}$ 等距嵌入 | 要求 $C^{1,\theta}\ (\theta > r/2)$ 时存在反例 |
| $r = 2$（$C^{1,1}$ 或 $C^2$） | 存在 $C^{1,\theta}\ (\theta < 1)$ 等距嵌入 | **要求 $C^{1,1}$ 或 $C^2$ 等距浸入/嵌入时均存在反例（本仓库主定理，对任意有限维 $\mathbb{R}^m$ 成立）** |
| $r > 2$ | 存在同正则性 $s = r$ 的等距嵌入（含 $C^{k,1},\ k \ge 2$，已由 `@dtq1997` 完成 Lean 核验） | 要求更高正则性 $s > r$ 时存在反例（含 $C^{k,1}$ 度量要求 $C^{k+1}$ 的情形） |


