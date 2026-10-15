[English](README.md) | [简体中文](README_zh.md)

# atomic-ionization-lean4

具有两种电子自旋态的完整非相对论库仑原子：一致电离界与广义电离渐近的 Lean 4 形式化。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，*Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms*（2026），定理 1.2 和推论 1.3；以及 *Generalized ionization energies for full Coulomb atoms*（2026），定理 1.1。论文稿及本形式化所依托的 Lean 库均见 [openai/math](https://github.com/openai/math)。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 主要结果

`AtomicIonization.main_theorem : AtomicIonization.Statement`，位于 [Main.lean](AtomicIonization/Main.lean)。

陈述位于 [Challenge.lean](AtomicIonization/Challenge.lean)，该文件只导入 Mathlib。固定一个电荷为整数 Z ≥ 1、位于原点的原子核；n 个具有两种自旋态的电子，其动能为 -Δ/2，受原子核吸引并彼此排斥，且波函数关于空间与自旋的联合变量反对称。能量 E_Z(n) 是反对称 H¹ 形式定义域中归一化向量上的库仑二次型下确界，并令 E_Z(0) = 0；I_m(Z) = E_Z(Z - m) - E_Z(Z)。中性原子的归一化基态是 n = Z 扇区中该形式的归一化极小值点；其半电子半径为 R(Ψ) = inf {r ≥ 0 : ∫_{|x|>r} ρ_Ψ ≤ 1/2}，其中 ρ_Ψ 是对自旋求和的一电子密度。Statement 断言：

1. 存在常数 0 < c ≤ C，使每个整数 Z ≥ 1 都满足 c ≤ I₁(Z) ≤ C；
2. 每个中性原子都有归一化基态；
3. 存在常数 0 < c ≤ C，使每个整数 Z ≥ 1 及其中性原子的每个归一化基态 Ψ 都满足 c ≤ R(Ψ) ≤ C；
4. 存在 a_TF > 0，它由 Thomas–Fermi 电离能满足 I_m^TF(Z) → a_TF m^{7/3}（Z → ∞）刻画；当 m → ∞ 且 Z / m → ∞，并且整数 1 ≤ m < Z 时，I_m(Z) / m^{7/3} → a_TF。

模型（形式定义域、能量形式、基态、密度、区域外质量）逐字取自 OpenAI 的 Comparator 陈述 `CoulombRadii`；Thomas–Fermi 刻画则取自其陈述 `CoulombIonization`。

最终定理只使用公理 `propext`、`Classical.choice` 和 `Quot.sound`。仓库中的证明均未使用 `sorry` 或新增公理。

## 构建与验证

环境要求：Git 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 在 `PATH` 中。在仓库根目录运行：

```sh
lake exe cache get
./scripts/verify.sh
```

第一条命令获取编译后的 Mathlib 缓存。脚本会构建库，并打印最终定理和各工作包定理所依赖的公理（[Verification/Axioms.lean](Verification/Axioms.lean)）。如果其中任何定理使用 `sorryAx` 或上述三个公理以外的公理，脚本就会失败。

v1.0.0 发行版的检查记录（全新克隆构建、使用 `leanchecker --fresh` 进行内核重放、使用 nanoda 内核运行 Comparator，以及对照检查）见 [docs/verification.md](docs/verification.md)。

## 目录结构

[Blueprint/Main.lean](AtomicIonization/Blueprint/Main.lean) 由工作包定理 `AtomicIonization.Blueprint.Packages.*` 推出 `Statement`；各定理的陈述位于 [Blueprint/Interfaces.lean](AtomicIonization/Blueprint/Interfaces.lean)。

| 工作包 | 内容 | 模块 |
| --- | --- | --- |
| `groundEnergy_eq_formBottom` | 扇区能量 = OpenAI 的形式下确界 | [ModelBridge/GroundEnergyEqFormBottom](AtomicIonization/ModelBridge/GroundEnergyEqFormBottom.lean) |
| `groundEnergy_le` | 扇区能量是归一化试探态的下界 | [ModelBridge/GroundEnergyLe](AtomicIonization/ModelBridge/GroundEnergyLe.lean) |
| `joint_limit` | Thomas–Fermi 联合极限，来自 OpenAI 的 `generalized_ionization` | [ModelBridge/JointLimit](AtomicIonization/ModelBridge/JointLimit.lean) |
| `ionization_upper` | `I₁(Z) ≤ C`（U，命题 12.3） | [UpperBound/IonizationUpper](AtomicIonization/UpperBound/IonizationUpper.lean) |
| `binding` | `E_Z(n) < E_Z(n-1)`，适用于 `1 ≤ n ≤ Z`（U，引理 2.5） | [AtomicBinding/Binding](AtomicIonization/AtomicBinding/Binding.lean) |
| `groundState_exists` | `1 ≤ n ≤ Z` 时的基态（U，引理 2.5） | [AtomicBinding/GroundState](AtomicIonization/AtomicBinding/GroundState.lean) |
| `ionization_gap` | 大 Z 时 `I₁(Z) ≥ c`（U，命题 13.1） | [IonizationGap/Package](AtomicIonization/IonizationGap/Package.lean) |
| `exterior_tail` | 区域外质量 `≤ C/R`（U，命题 14.1） | [ExteriorTail/Tail](AtomicIonization/ExteriorTail/Tail.lean) |
| `radius_lower_large` | 大 Z 时 `R(Ψ) ≥ c`（U，第 12 节） | [HalfRadius/Large](AtomicIonization/HalfRadius/Large.lean) |
| `radius_bounds_fixed` | 每个固定 Z 下半径的双侧界（U，第 14 节） | [HalfRadius/Fixed](AtomicIonization/HalfRadius/Fixed.lean) |

这里的 U 指 *Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms*。形式化证明遵循论文，但部分步骤改用了不同路线：命题 14.1 中对重新加权后的基态应用测度变换；命题 13.1 使用平滑乘子；束缚性和固定电荷半径的步骤则用直接估计代替 Newton 定理和紧性论证。

[OAI/](OAI) 中存放 OpenAI 的库 `CoulombRadii` 和 `CoulombIonization`，未作改动；见 [THIRD_PARTY.md](THIRD_PARTY.md)。
