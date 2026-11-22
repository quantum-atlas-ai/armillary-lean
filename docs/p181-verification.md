# p181 精确距离验证

`p181` 是码长 8688 的 Armillary CSS 码。Lean 定理 `ArmillaryLean.CodeP181.distance_eq_sixteen` 对源路由构造的 `code` 证明 `cssDistance code = 16`。定理在验收时生成，模块名为 `ArmillaryLean.Instances.ReducedProof.CodeP181.Exact`。 [最终证明及公理审计](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44974973997/job/137064402518)

## 证明覆盖

- **上界。** Lean 核验作者给出的重量 16 纯 X 逻辑见证，证明它与 Z 校验正交并位于 X 稳定子行空间之外。 [码的构造与上界](../ArmillaryLean/Instances/CodeP181.lean)
- **下界。** Lean 证明零综合征支撑必有偶数重量，借助稳定子减重和循环平移把低重量候选归约到 X、Z 校验侧各 48 个锚点。证书排除了归约后重量至多 14 的候选，因此排除了重量小于 16 的非平凡逻辑算符。 [锚点归约](../ArmillaryLean/Instances/RoutedAnchors.lean) · [证书检查器](../ArmillaryLean/Certificates/Reduced.lean)
- **精确等式。** 汇总任务把 96 个锚点各自的排除定理交给 `distance_eq_sixteen_of_anchors`，与上界合成精确距离。最终定理的传递公理依赖为 `propext`、`Classical.choice` 和 `Quot.sound`。 [等式接口](../ArmillaryLean/Instances/ReducedDistances.lean)

## 验收记录

2026 年 11 月 22 日，全量验收完成。候选证书先通过独立离线回放，本地 Lean 随后检查 37,974 个证书页并组装 96 个锚点。冻结制品包括 1 个公共依赖包和 16 个分片，总计约 10.5 GB。 [冻结制品](https://github.com/quantum-atlas-ai/armillary-lean/releases/tag/p181-proof-v1)

GitHub Actions 从发布版本下载制品并核对摘要。每个分片任务导入本地编译的制品并审计公开和私有声明的传递公理。汇总任务核对全部回执及公开证明对象的摘要，再用这些对象在 Lean 中构建最终等式并审计其公理。整个云端工作流历时 9 分 53 秒。 [完整审计运行](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44974973997) · [工作流](../.github/workflows/certificates.yml) · [分片审计脚本](../tools/p181_split.py)

| 项目 | 固定值 |
| --- | --- |
| 发布标签 | `p181-proof-v1` |
| 证明提交 | `66255a1b461284cada02f2a31c123d06cdb2b65d` |
| 工具链与平台 | Lean `v4.35.0`，Linux `x86_64` |
| `p181-manifest.json` 的 SHA-256 | `77e2b909b04bd3877dc52bbc2695aae48f73ce8ea11ed26247b61434e9011384` |

## 重跑云端审计

用有工作流触发权限的 GitHub 账号执行以下命令。工作流在制品标签固定的证明提交上运行，复用已编译的证书页和锚点。成功的汇总任务将生成的 `Final.lean` 和 `Final.olean` 放入 `p181-assembled-proof` 制品。 [最终定理制品](https://github.com/quantum-atlas-ai/armillary-lean/actions/runs/44974973997/artifacts/14735946180)

```bash
gh workflow run certificates.yml \
  --repo quantum-atlas-ai/armillary-lean \
  --ref p181-proof-v1 \
  -f proof=p181-split \
  -f proof-release=p181-proof-v1 \
  -f proof-sha256=77e2b909b04bd3877dc52bbc2695aae48f73ce8ea11ed26247b61434e9011384
```
