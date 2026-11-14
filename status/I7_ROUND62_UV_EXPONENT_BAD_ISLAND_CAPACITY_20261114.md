# 第62轮：I7 一环尾项阶数、真实SU2局部响应及坏场容量审计

日期：2026-11-14
分支：ym-i7-uv-exponent-capacity-20261114
继承：ym-i7-numerical-geometric-20261114 @ 653fcc3828d8d0ae20599511ef8d6fe89a3d83e4

## 0. 验收边界

原始 39/39 定理环境仍为 CONDITIONALLY PASS（I7为显式假设）。
真实四维 SU(2) 物理 I7：OPEN。连续体 Clay 质量隙：OPEN。
本轮没有新增 Lean 定理，不以增加条件性环境计数替代动力学证明。
全部数值为精确 SU2 Haar/Bessel 群积分、组合枚举和一环 RG 模型；并非四维 Yang–Mills 的连续体证据。

## 1. 四维裸单链路 Dobrushin 的真实几何下界

在 4D 超立方格上，一条内部链路 e 恰好属于六个 plaquette（每个其它方向各有前后两个），每个 plaquette 另有三条边。直接以整数坐标枚举，18条相邻链路两两不同（空间尺寸足够大，避免小环面退化）。

令 SU(2) 同构单位四元数 S³。固定其余链路后，带标准 Wilson 逆耦合 beta_W 的单链路条件分布为

  d nu_eta(u) = Z(eta)^(-1) exp(eta.u) d Haar(u),
  eta=beta_W * sum_{p: p contains e} s_p,

其中 s_p 为对应的单链路 staple 四元数。每个其它邻链路恰好改变其中一个 staple。可选择三个 s_p=+1、三个 s_p=-1，使 eta=0，故 nu_eta=Haar。对于所有扰动方向 i=1,2,3，1-Lipschitz 函数 f(u)=u_i 有

  d/dt E_nu_{t v}[f] |t=0
    = Cov_Haar(u_i, v.u) = v_i/4,

因为 E_Haar(u_i u_j)=delta_ij/4。将一条邻链路旋转角 epsilon，边界 chordal 距离 delta=2sin(epsilon/2)，得到严格的小角差商极限

  lim_eps->0 W1(nu_eta,nu_eta')/delta >= beta_W/4.

因此 Dobrushin 影响系数 C_{e,e'} >= beta_W/4（supimum over exteriors），其行和满足

  sum_{e' != e} C_{e,e'} >= (18/4)*beta_W = 9 beta_W/2.

若 beta_W>=2/9，原未规范固定单链路 Dobrushin 行和不可能小于1。这是现有2026 Bhattacharjee et al. 预印本（One Cube Estimate Implies the Yang--Mills Mass Gap, v7, Theorems 1–2及开篇）记载的已知尖锐阈值，本轮仅独立核验几何和 Haar 导数，**不是发现新的 SU(2) 质量隙结果**。

在所有六个 staple 都对齐单位四元数的光滑背景，同一个局部线性响应给出第二个下界：

  sum_{e'} C_{e,e'} >= 3 * I_2(6 beta_W) / I_1(6 beta_W).

这里I_ν为修正Bessel函数。该下界在 beta_W≈0.24075803 时已超过1，beta_W=2.3时为约2.68030，而零场最坏背景下界为10.35。说明**即使在平滑背景中裸链路单点收缩也可能失败**。

注意：此结果只针对未规范固定的裸链路 Wasserstein Dobrushin 判据；森林规范固定、多链路块的 Dobrushin–Shlosman 条件和完整 OS 传递谱并不随之失效。该预印本 v7 在三链路块规则下报告 SU2 强耦合区 beta_W<=0.348 的结果，但仍未证明连续调参路线的物理立方体估计或4D连续体质量隙。
数据：I7_round62_exact_vmf_influence.csv, I7_round62_dobrushin_method_obstruction.png。

## 2. 真实 Lean U1 接口的紫外指数预算

在反向 RG 模型 g_{K-j}²=1/(A_*+b j)，j越大越靠紫外。
若单尺度**真实、匹配物理 Wilson 源**的误差绝对值受 C*g^{p} 控制，则
  sum_{j=N}^infinity g_{K-j}^{p}
   =sum_{j=N}^infinity (A_*+bj)^(-p/2).

严格的积分判别法说明该无额外尺度加权的和收敛当且仅当 p>2。
在 p>2 时：
  S_p(N) <= (A_*+bN)^(-p/2)
       +(A_*+bN)^(1-p/2)/[b(p/2-1)] ->0.
p=2对应调和级数对数发散；p<2幂次发散。

现有公开 Lean 文件
  Lean/Section02/T001_U1_PublishedInterface.lean
  YMOriginal/Original24_WeakU1Margin.lean
所用 oldR 活动因子 g^{kappa0} 的 small-coupling 验收仅要求
kappa0>0；newR 因子 exp(-p0(g)) 的验收只要求 p0(g)->+infinity。
这些前提 **不足以单独推出 unweighted RG UV tail 可求和**。
例如 p0(g)=log(1/g) 也趋于无穷，但 newR 的渐近因子只有 g，相关紫外总和发散。
要补齐这条采用直接绝对求和的主链，需要下列方案之一：

  (i) oldR kappa0>2, 且 newR exp(-p0(g)) <= C*g^{2+delta};
  (ii) 额外具有严格一致的几何尺度因子 L^{-sigma j}，sigma>0;
  (iii) 真正的跨尺度抵消/反项，使未补偿的有效余项高于二阶。

原Bałaban文献在某些定理中可选较大kappa0，但选择此参数、真实源/jet字典、尺度一致性及newR的具体 p0 仍需以其原精确范围核验；不可把字面 kappa0>0 自动等价于kappa0>2。
*这只是纯绝对求和技术的临界门槛，不能当成 Yang--Mills 物理模型的必要条件。*

## 3. “大场岛很罕见”不推出统一谱隙：严格反例与容量形式

考虑状态空间 {G,B} 的可逆离散转移，在稳态 pi(B)=epsilon, pi(G)=1-epsilon 下设
  P(B,G)=delta=epsilon^2,
  P(G,B)=epsilon*delta/(1-epsilon),
其余概率由行和为1确定。显然
  pi(G)*P(G,B)=pi(B)*P(B,G)=epsilon*delta,
故详细平衡。两个特征值恰好为
  1,
  lambda_nonvac=1-delta/(1-epsilon).
从而谱隙恰为
  gap=delta/(1-epsilon)=epsilon^2/(1-epsilon)->0,
尽管坏状态概率pi(B)=epsilon->0。

一般可逆Markov转移P与任意事件A的指标测试向量
  f=1_A-pi(A)
满足
  <f,(I-P)f>=Q(A,A^c),
  ||f||²=pi(A)(1-pi(A)),
其中 Q(A,A^c)=int_A P(x,A^c) pi(dx) 是跨集合的稳态概率流。因此
  gap(P) <= Q(A,A^c)/[pi(A)(1-pi(A))].
若要由大场-小场分解建立正质量隙，不能仅证明大场事件概率小；还需排除“极罕见但逃逸更慢”的坏场陷阱（容量/导通性下界）。

这只是严格马尔可夫谱论反例，并不构成 Yang–Mills 的反例。把它用于实际Wilson/OS物理算子须先证明正确的ground-state变换及Markov正性；不可拿普通Euclidean Gibbs条件期望自动当作OS投影（第60轮已给出反例）。

数据：I7_round62_rare_island_summary.csv 和 I7_round62_rare_island_spectral_trap.png。

## 4. 最短B14两次极限主线可以进一步放松q_N的量词

保留第59轮 Lean 已严格通过的：
  b14_continuum_gap_from_vanishing_cutoff_defect
  original42_continuum_only_from_same_schwinger_gram.

以一共同固定物理时间t和同一Schwinger/OS来源为前提，设
  Q_{t,k}(F) <= q_N Q_{0,k}(F) + E_N(F)+C_N(F)*xi_k
在每个固定 N、固定有限物理Wilson测试源F时沿同一联合截止体积极限最终成立。
只需
  0<=q_N<=1,
  limsup_{N->infty}q_N = q_* <1,
  E_N(F)->0（每个固定F）,
  xi_k->0,
  C_N(F)<infty
和Q0/Qt同网收敛。先固定N，令k趋于极限，再让N->infty：

  Q_{t,cont}(F) <= q_N Q_{0,cont}(F)+E_N(F)
  Q_{t,cont}(F) <= q_* Q_{0,cont}(F).

再取任意q满足max(0,q_*)<q<1，所有有限源获得严格Gram收缩，稠密延拓得物理连续体生成元质量隙>=-log(q)/t>0。

相较第59轮，允许终端的q_N随最后N个RG层变化，不再需要同一个固定q对所有N成立；**但必须验证 limsup_N q_N<1，而不是仅每个q_N<1**。例如q_N=1-1/N时虽每个N严格小于1，却无法得出统一隙。

只有证明对完整真实Wilson终端有效作用的q_N，且实现真实OS/Schwinger来源/联合极限，才能启动已形式化的B14主链；这些物理生产者目前完全OPEN。
该q_N-variable两次极限结果为纸面数学证明，本轮不为增加比例再新增Lean定理。

## 5. 第62轮闭合树

4D SU(2) U–I–C
|-- GREEN: 历史39/39条件性证明结构保持
|-- GREEN: 第55–59轮16条严格辅助Lean结果保持
|-- GREEN: 本轮真实SU2单链路Haar导数、18邻链路和Dobrushin方法障碍
|-- GREEN: 一环模型UV尾项p>2临界指数严格导出
|-- GREEN: 罕见坏场谱陷阱精确反例与容量必要条件
|-- GREEN: variable q_N 两次极限纸面桥
|-- YELLOW: 真实UV RG余项得到p>2或几何尺度因子，并与同一Schwinger测试源匹配
|-- YELLOW: 连续体OS来源/时标/正时间稠密性与真实Wilson转移一致
|-- RED: 完整终端非微扰SU2模型limsup_N q_N<1，且无罕见坏场陷阱
|-- then: B14 同网极限 -> 连续体正质量隙
|-- actual physical I7 OPEN, unconditional Yang–Mills mass gap OPEN.

## 6. 参考与独立复现

- One Cube Estimate Implies the Yang–Mills Mass Gap, v7 (2026), https://hexagonmath.org/2610.00341v7，详见引言Dobrushin阈值、Theorems1–3及Appendix K。其自身明确声明沿连续体调参轨道的立方体估计仍未闭合。
- Bałaban RG I, CMP 109 (1987), 249–301, DOI 10.1007/BF01215223.
- Bałaban Large field RG II, CMP 122 (1989), 355–392, DOI 10.1007/BF01238433.
- Michael Douglas, The Yang–Mills Millennium problem, Nature Reviews Physics 8 (2026), 86–97.
- 完整可复现Python、数值CSV和三张图见本轮对话产物 I7_round62_analytic_numerical_bundle.zip。
