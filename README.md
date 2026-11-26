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
