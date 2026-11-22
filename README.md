# Armillary Lean

[![Lean CI](https://github.com/quantum-atlas-ai/armillary-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/quantum-atlas-ai/armillary-lean/actions/workflows/ci.yml)

本仓用 Lean 形式化 *Rate-1/2 Quantum LDPC Codes for Multi-tier Superconducting Hardware* 中的具体 Armillary 码实例。校验矩阵来自论文路由，距离和其他实例证书消费 Qatlib 的通用纠错码接口。 [arXiv:2611.20410v1](https://arxiv.org/abs/2611.20410v1)

| 实例 | 码长 | 已在 Lean 证明 | 验收记录 |
| --- | ---: | --- | --- |
| `8749` | 3636 | `d = 12` | [精确距离定理](ArmillaryLean/Instances/MinProof8749/Exact.lean)，远端全量重建待补 |
| `9053` | 4932 | `d = 14` | [完整远端验收与公理审计](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44336436018) |
| `p181` | 8688 | `d = 16` | [分片审计与精确距离汇总](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44974973997) · [验证与复验说明](docs/p181-verification.md) |

## 形式化验证范围

1. **从源路由构造静态 CSS 码。** Lean 根据记录的通道排列、位移和保留校验组构造二元 X/Z 校验矩阵，证明矩阵与路由的关联一致，核对各实例的码长，并证明 CSS 正交性 `H_X H_Zᵀ = 0`。 [8749 构造](ArmillaryLean/Instances/Css8749.lean) · [9053 构造](ArmillaryLean/Instances/Code9053.lean) · [p181 构造](ArmillaryLean/Instances/CodeP181.lean)
2. **核验逻辑算符见证并证明距离上界。** 对每个实例，Lean 核验给定的纯 X 见证有相应重量、与 Z 校验的交叠为偶数，并用分离向量证明它在 X 稳定子行空间之外。因此它是非平凡逻辑算符，给出表中的距离上界。 [8749 见证](ArmillaryLean/Instances/Upper8749.lean) · [9053 见证](ArmillaryLean/Instances/Code9053.lean) · [p181 见证](ArmillaryLean/Instances/CodeP181.lean)
3. **排除更低重量的逻辑算符。** Lean 证明零综合征支撑必有偶数重量，并用平移对称性把待排除的支撑归约到有限个锚点，即归约后必须包含的指定坐标。`9053` 和 `p181` 还用稳定子减重保留逻辑等价类。证书排除各锚点下的低重量候选后，下界定理与上界合成精确距离。 [8749 下界](ArmillaryLean/Instances/Lower8749.lean) · [归约定理](ArmillaryLean/Instances/RoutedAnchors.lean) · [精确距离接口](ArmillaryLean/Instances/ReducedDistances.lean)
4. **检查证书和证明依赖。** 仓库提供候选证书的搜索和独立回放工具。Lean 核对证书使用的校验行与源矩阵，并通过检查器的可靠性定理把接受结果转成排除结论。验收记录分别标明离线回放、Lean 内核检查和公理审计；公理审计只允许 `propext`、`Classical.choice` 和 `Quot.sound`。 [8749 数值检查器](ArmillaryLean/Certificates/Numeric.lean) · [约简检查器](ArmillaryLean/Certificates/Reduced.lean) · [公理审计脚本](tools/audit_axioms.py)

现有定理覆盖静态 CSS 构造和距离。精确校验秩、逻辑比特数、Tanner 围长、实际综合征提取线路及硬件噪声模型列在[后续工作](#后续工作)。

## 数据来源

实例参数和逻辑见证与作者的 `Armillary-codes` 仓库提交 `f5a9c17dfa47118b4dd56743d934d98865a2b2e9` 中的数据逐项一致。各目录的 `candidate.json` 记录路由参数，`logical_witness.json` 记录逻辑算符支撑。公开预印本补充材料的 Table S2–S4 给出相同的路由参数。 [8749 数据](https://github.com/Jiaxuan-quantum/Armillary-codes/tree/f5a9c17dfa47118b4dd56743d934d98865a2b2e9/hardware_layouts/data/d12) · [9053 数据](https://github.com/Jiaxuan-quantum/Armillary-codes/tree/f5a9c17dfa47118b4dd56743d934d98865a2b2e9/hardware_layouts/data/d14) · [p181 数据](https://github.com/Jiaxuan-quantum/Armillary-codes/tree/f5a9c17dfa47118b4dd56743d934d98865a2b2e9/hardware_layouts/data/d16)

## 实例 9053 和 p181

两份实例对应 Table S3 和 S4。Lean 验证源路由给出的 CSS 正交性，再通过 Z 校验行内的配对抵消以及块 `0, 1` 的分离向量，证明两个纯 X 逻辑见证给出上界。 [9053 上界](ArmillaryLean/Instances/Code9053.lean) · [p181 上界](ArmillaryLean/Instances/CodeP181.lean)

下界归约证明了翻转交叠超过 6 的重量 12 稳定子行可以严格减重，并保持 syndrome 与稳定子陪集。循环平移将减重后的支撑移到 station-zero 最小锚点，同时保持对每条稳定子行的交叠数。`distance_eq_fourteen_of_anchors` 和 `distance_eq_sixteen_of_anchors` 分别把两侧完整的锚点排除证书合成为目标等式。 [稳定子约简](ArmillaryLean/Certificates/Stabilizer.lean) · [锚点归约](ArmillaryLean/Instances/RoutedAnchors.lean) · [等式接口](ArmillaryLean/Instances/ReducedDistances.lean)

`9053` 还有一个经过 Lean 验证的扇区互换。它用同一个数据坐标双射互换两套校验行，同时保持 syndrome 和稳定子交叠。`distance_eq_fourteen_of_x` 因此只需要 X 校验侧的 36 个锚点。 [扇区互换](ArmillaryLean/Instances/Swap9053.lean)

Lean 定理 `ArmillaryLean.Code9053.distance_eq_fourteen` 证明了 `cssDistance code = 14`。完整验收使用异或剪枝证书核验了全部 36 个 X 侧锚点，并汇总为模块 `ArmillaryLean.Instances.ReducedProof.Code9053.Exact`。公理审计结果为 `propext`、`Classical.choice` 和 `Quot.sound`。 [完整验收记录](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44336436018) · [定理汇总与公理审计](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44336436018/job/134946990731)

Lean 定理 `ArmillaryLean.CodeP181.distance_eq_sixteen` 证明了 `cssDistance code = 16`。全部 96 个下界锚点及其 37,974 个证书页通过本地 Lean 检查。GitHub Actions 审计了固定制品的全部 16 个分片，复核覆盖后构建精确距离定理，公理依赖为 `propext`、`Classical.choice` 和 `Quot.sound`。 [最终汇总及公理审计](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44974973997/job/137064402518) · [固定制品](https://github.com/quantum-atlas-ai/armillary-lean/releases/tag/p181-proof-v1)

### 约简证书生成与核验

两个实例全部 168 个 X/Z 锚点已有候选树，并通过独立离线回放。Lean 的约简检查器支持校验行封闭、packing、分裂、稳定子交叠及异或 packing。Lean 对照源路由核对校验行表，并检查各实例精确距离证明需要的锚点。 [检查器](ArmillaryLean/Certificates/Reduced.lean) · [源路由表示](ArmillaryLean/Instances/ReducedNumeric.lean)

完成本仓默认构建后，可生成两个实例的证书并独立回放。最后两个命令调度正式内核检查，并在全部目标通过后构建相应精确距离模块。大部分运行时间在编号较小的锚点，日志写入 `.lake/reduced/build-logs`。

```bash
lake --no-build lean tools/ExportReducedRows.lean
c++ -O3 -std=c++20 tools/search_reduced.cpp -o .lake/reduced/search
c++ -O3 -std=c++20 tools/replay_reduced.cpp -o .lake/reduced/replay
for spec in '137 3 12' '181 4 14'; do
  read -r p q budget <<< "$spec"
  packing=()
  if [[ "$p" == 137 ]]; then packing=(--xor); fi
  for pair in 'X Z' 'Z X'; do
    read -r opposite stabilizers <<< "$pair"
    O=".lake/reduced/$p-$opposite.rows"
    S=".lake/reduced/$p-$stabilizers.rows"
    B=".lake/reduced/$p-$opposite.bin"
    .lake/reduced/search "$O" "$S" "$p" "$q" "$budget" 0 "$((12*q))" --binary "${packing[@]}" > "$B"
    .lake/reduced/replay "$O" "$S" "$p" "$q" "$budget" 0 "$((12*q))" "$B"
  done
done
python3 tools/build_reduced.py 9053 --jobs 4
python3 tools/build_reduced.py P181 --jobs 4
```

## 实例 8749

Lean 定理 `ArmillaryLean.Code8749.distance_eq_twelve` 证明了 `cssDistance code = 12`。完整证明入口为 `import ArmillaryLean.Instances.MinProof8749.Exact`。公理审计结果为 `propext`、`Classical.choice` 和 `Quot.sound`。 [定理源码](ArmillaryLean/Instances/MinProof8749/Exact.lean)

`Data8749.lean` 保存补充材料 Table S2 的保留组、通道排列和位移。数据模块还记录作者的逻辑见证，并证明它包含 12 个互异坐标。 [数据模块](ArmillaryLean/Instances/Data8749.lean)

`Code8749.lean` 将源参数接到 `Qatlib` 路由，定义 X/Z 校验矩阵，并证明码长为 3636、列重为 3、矩阵关联与路由访问等价，以及访问关系在循环平移下的相容性。 [路由与校验矩阵](ArmillaryLean/Instances/Code8749.lean)

[`Css8749.lean`](ArmillaryLean/Instances/Css8749.lean) 核验块配对并构造具体 CSS 码。[`Upper8749.lean`](ArmillaryLean/Instances/Upper8749.lean) 对三个保留 Z 校验组逐一核验支撑的成对抵消，再用块 `0` 和 `3` 上的分离向量排除 X 稳定子行空间，得出 `distance_le_twelve`。

## 下界证书

[`Lower8749.lean`](ArmillaryLean/Instances/Lower8749.lean) 证明源校验矩阵的零 syndrome 等价于稀疏邻域偶交叠，并推出偶重量与 station-zero 锚点归约。[`Exact8749.lean`](ArmillaryLean/Instances/Exact8749.lean) 证明两套锚点排除结论足以与已验证的上界合成精确距离。

[`Masked.lean`](ArmillaryLean/Certificates/Masked.lean) 证明 512 位分块检查器的接受结果能传递到集合版，后者证明封闭叶与 packing 叶的排除有效。[`Rows8749.lean`](ArmillaryLean/Instances/Rows8749.lean) 的查表数据逐项核对了源路由，[`Anchor8749.lean`](ArmillaryLean/Instances/Anchor8749.lean) 将位掩码中的关联传递回具体源矩阵。

`ArmillaryLean.Code8749.sample_excludes` 验收了 X 校验矩阵在 `(0, (0, 0))` 上重量至多 4 的排除，可用于复现分块检查器的行为。 [样例证书](ArmillaryLean/Instances/Sample8749.lean)

在同一 X 校验锚点上，重量上限 4 的集合版与分块版分别约用 26 秒和 16 秒。重量上限 6 的集合版超过 180 秒，分块版约用 91 秒并通过内核验收。重量上限 8 和 10 的分块版分别超过本次设定的 170 秒和 155 秒。耗时包含 Lake 启动。

下列命令复现最初的双侧候选树和离线回放。X/Z 是校验矩阵的名称，锚点序号为 `3 * block + channel`。

```bash
lake --no-build lean tools/ExportRows8749.lean
c++ -O3 -std=c++20 tools/search8749.cpp -o .lake/dist8749/search8749
for checks in X Z; do
  .lake/dist8749/search8749 ".lake/dist8749/$checks.rows" 10 0 36 > ".lake/dist8749/$checks-10.words"
  python3 tools/replay8749.py ".lake/dist8749/$checks.rows" ".lake/dist8749/$checks-10.words" --budget 10
done
```

重量上限 4 的内核样例可独立复现。使用 `--checker finset` 可以在同一份数据上比较集合版。

```bash
.lake/dist8749/search8749 .lake/dist8749/X.rows 4 0 1 > .lake/dist8749/X0-4.words
python3 tools/render8749.py .lake/dist8749/X0-4.words .lake/dist8749/Probe8749.lean \
  --checks X --anchor 0 --budget 4
lake --no-build lean .lake/dist8749/Probe8749.lean
```

渲染时加 `--fragment-words 20` 会在实际分支处切开同一份样例。Lean 独立核验各片段，并用已证明的分支组合定理得出根状态的排除结果。重量上限 6 的样例使用 `--fragment-words 100` 复现，约用 53 秒通过内核验收。重量上限 10 的实际证书切分后，首个独立片段约用 12 秒通过内核验收，整个锚点仍超过本次设定的 155 秒。

### 最小锚点与数值验收

[`Symmetry8749.lean`](ArmillaryLean/Instances/Symmetry8749.lean) 在源路由上证明了 X、Z 校验图同构。X 校验侧的最小锚点排除因此足以证明精确距离。每个支撑只需考虑块与通道编号最小的锚点，最后一块的三个锚点由单块论证直接排除。

[`Numeric.lean`](ArmillaryLean/Certificates/Numeric.lean) 用自然数位图检查其余 33 个 X 侧锚点。Lean 内核核验了全部证书以及行字表与源路由的一致性。零 syndrome 的支撑重量必为偶数，因此排除重量至多 10 的非空支撑也排除了重量 11。

完成下文的本地检查后，先导出校验行，再生成最小锚点证书、离线回放，并分模块完成 Lean 构建。`HeadX*.lean` 由脚本在本地生成，`Exact.lean` 是仓库中的证明入口。最后一次构建会输出定理的公理审计。

```bash
lake --no-build lean tools/ExportRows8749.lean
c++ -O3 -std=c++20 tools/search8749.cpp -o .lake/dist8749/search8749
.lake/dist8749/search8749 .lake/dist8749/X.rows 10 0 36 --minimum > .lake/dist8749/MinX.words
python3 tools/replay8749.py .lake/dist8749/X.rows .lake/dist8749/MinX.words --budget 10 --minimum
python3 tools/build_min8749.py .lake/dist8749/MinX.words --jobs 4
```

## 后续工作

- **补充 `8749` 的远端全量重建验收。** 上一次重建中，两个任务写入共享 `.ilean` 时出现权限错误。 [重建记录](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44312530324)
- **验证三个实例的精确 Tanner 围长。** 在已有的 X/Z 校验矩阵上，各自核验一个长度为 6 的圈，并排除长度为 4 的圈。
- **验证精确校验秩和逻辑比特数。** 在两侧分别核验 GF(2) 秩下界证书，与结构给出的秩上界合成等式。目标分别是 `8749` 的秩 907、`k = 1822`，`9053` 的秩 1231、`k = 2470`，以及 `p181` 的秩 2170、`k = 4348`。
- **接通正反轮的测量语义。** 由论文的 CXSWAP 与 SWAP-only 调度生成实际线路，验证门方向、迭代后的角色位置以及联合 syndrome 的测量分支。随后分别跟踪 Armillary 线路资源、线路级故障距离、硬件布局和论文噪声模型的验证。

## 本地检查

Lean 工具链固定为 `v4.35.0`，`Qatlib` 固定为 `5c88a0b7275769d44542d0a371a5af8f8841cbae`。本仓用 Lake 检查 `ArmillaryLean`，并消费上游的预编译制品。首次检出时先准备锁定版本的依赖缓存。 [Qatlib 缓存指南](https://github.com/quantum-atlas-ai/qatlib/blob/5c88a0b7275769d44542d0a371a5af8f8841cbae/docs/getting-started.md)

在仓库根目录先用 `--no-build` 确认两个上游入口的缓存可用。通过后构建本仓顶层导入。

```bash
lake --no-build build +Qatlib.Papers.Armillary26.Instances.Routed \
  +Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance
lake build +ArmillaryLean
python3 tools/audit_axioms.py
```

`Lean CI` 在推送和拉取请求上构建本仓、检查内核证书样例并审计传递公理。仅改动根目录 `README.md` 时跳过自动构建，也可按需手动触发。`Kernel certificates` 工作流可手动重建并核验 `8749` 的完整证明，或选取 `9053`、`p181` 的一个 sector 和锚点进行核验。锚点运行的构建日志随本次运行保存。`p181-split` 模式从发布制品执行完整公理审计和最终定理汇总。 [p181 复验命令](docs/p181-verification.md#重跑云端审计) [Lean CI](https://github.com/quantum-atlas-ai/armillary-lean/actions/workflows/ci.yml) · [Kernel certificates](https://github.com/quantum-atlas-ai/armillary-lean/actions/workflows/certificates.yml)

`Exact 9053 distance` 工作流用异或剪枝生成 X 侧的 36 个证书，分片验收后汇总并审计精确距离定理。 [完整 9053 验收](https://github.com/quantum-atlas-ai/armillary-lean/actions/workflows/exact-9053.yml) · [冻结制品的远端审计](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44451282907)

## 许可

本仓代码采用 Apache-2.0。来自作者 `Armillary-codes` 仓库的实例参数和逻辑见证附有原 MIT 版权和许可声明。 [Apache-2.0](LICENSE) · [作者 MIT 许可](LICENSES/Armillary-codes-MIT.txt)
