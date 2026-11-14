# 第67轮｜I7纸面证明：三空间向 SU2 矩阵量子束缚及物理体积尺度审计

日期：2026-11-14
研究分支：ym-i7-round67-matrix-volume-20261114
继承：ym-i7-round66-one-sided-leakage-20261114
验收：原始 39/39 仍然只在显式 I7/其它物理输入下 CONDITIONALLY PASS。
真实4D SU2 原 I7 未闭合；本轮遵循纸面优先，没有新增 Lean 环境或 CI；无 Clay 问题解决声明。

## A. 新严格纸面引理：三个空间方向的非阿贝尔量子束缚（更一般 m>=2）

对 m>=2、g>0，定义玻色 SU2-Lie-algebra 矩阵量子力学
  H_(g,m) = - sum_(i=1)^m Delta_(x_i)
            + g² sum_(1<=i<j<=m)|x_i cross x_j|²
作用于 L²((R³)^m)，Friedrichs自伴实现。

取 0<theta<1，对有序对 i!=j 定义
  A_(i,j) = -[(1-theta)/(m-1)] Delta_(x_j)
             + (g²/2)|x_i cross x_j|².

精确有
  H_(g,m)= -theta sum_i Delta_(x_i) + sum_(i!=j) A_(i,j).
固定 x_i，将其旋转到第三坐标轴，x_j 的两个垂直方向为
二维谐振子，其基本能量为
  2sqrt( [(1-theta)/(m-1)]*(g²/2) )|x_i|
    =g sqrt(2(1-theta)/(m-1)) |x_i|.
从而对任意 C_c^\infty 波函数，二次型意义下
  H_(g,m) >= -theta sum_i Delta_(x_i)
         +g sqrt(2(m-1)(1-theta)) sum_i |x_i|.

取 theta=1/2，得到
  (67.1-general)
  H_(g,m) >=sum_i[-(1/2)Delta_(x_i)+g sqrt(m-1)|x_i|].

对单个 R³ 的径向线性势 h=-a Delta+b|x|，
角动量 l=0 的径向变换 u(r)=r f(r) 给出
  -a u''+b r u = E u, u(0)=0,
E_0(h)=a_1(a b²)^(1/3),
a_1=2.338107410459767... 是 Ai(-a_1)=0 的首根。
角动量 l>0 添加非负 l(l+1)/r²，不能降低基态。

于是得到显式严格下界
  E0(H_(g,m))
   >= m a_1 ((m-1)/2)^(1/3) g^(2/3).

选各向同性归一 Gaussian ψ_α =
 (α/π)^(3m/4) exp[-α sum_i |x_i|²/2]，
可精确计算
  < -sum Delta >=3m α/2,
  <|x_i cross x_j|²>=3/(2α²).
所以
  E0(H_(g,m))
     <= 3m α/2+ [3m(m-1)/(4α²)]g²,
取 α³=(m-1)g² 的最优试探值得到
  E0(H_(g,m))
     <=(9m/4)(m-1)^(1/3) g^(2/3).

严格夹逼：
  m a_1 ((m-1)/2)^(1/3) g^(2/3)
    <=E0(H_(g,m))
    <=(9m/4)(m-1)^(1/3) g^(2/3).

特别 m=3：
  7.014322231379302 g^(2/3)
  <=E0(H_(g,3))
  <=8.504467086790394 g^(2/3).

由上面的线性束缚势二次型控制，H_(g,m) 的形式域紧嵌入L²，
故算子具有紧预解式（纯离散谱）。势连续、定义域连通，
热核正性改进/基态唯一性进一步给出
  Delta_(g,m):=E1(H_(g,m))-E0(H_(g,m))>0.
坐标尺度变换保证
  Delta_(g,m)=g^(2/3) Delta_(1,m).
注意：显式基态**能量**下界不是显式激发谱隙下界。
不能把常数7.014误写成质量隙数值。

本有限维量子束缚机制与 Barry Simon,
"Some quantum operators with discrete spectrum but classically continuous spectrum",
Annals of Physics 146 (1983), 209--220,
DOI 10.1016/0003-4916(83)90057-X 同一类思想。
不主张为新的四维 Yang--Mills 物理定理。

## B. 关键新尺度阻断：整个空间齐次 SU2 振子的gap并不体积一致

令空间为物理边长 L 的三维环面。
在只保留三个空间均匀 su2 Lie-algebra 场 A_i 的
**齐次零模量子力学截断**中，常见归一化取
  H_hom(L,g)= -[g²/(2L³)]sum_i Delta_(A_i)
              +[L³/(2g²)]sum_(i<j)|A_i cross A_j|².
为保持确切形式，在此模型中坐标 A_i 取非紧 R³；
这是带规定范围的齐次 MODEL，不是紧群真实
Kogut–Susskind 完整 Hamiltonian 的酉同构。

作精确尺度变换
  A_i=(g^(2/3)/L) x_i.
则
  H_hom(L,g) \cong [g^(2/3)/(2L)] H_(1,3).

因此
  E_n(L,g)=[g^(2/3)/(2L)] E_n(1,3),
  Delta_hom(L,g)=[g^(2/3)/(2L)]Delta_(1,3).

对固定g>0，
  Delta_hom(L,g)->0 as L->infty,
虽然每一个固定有限L都严格有隙。

数值交叉核验（g=1）：
 L | 严格E0下界 | Gaussian E0上界
  2     1.7535806     2.1261168
  4     0.8767903     1.0630584
  8     0.4383951     0.5315292
 16     0.2191976     0.2657646
 32     0.1095988     0.1328823
 64     0.0547994     0.0664411.

这从量纲上解释第66轮的局部非阿贝尔量子束缚
为何仍没有提供原I7需要的*空间体积一致*质量隙。
**不能反向声称真实SU2 4D没有质量隙**：
齐次截断不包含非均匀空间模态的量子效应，
且在L≫ΛYM^(-1)时，固定弱g或一环运行的近似已失效；
非零模态与齐次模态强烈耦合。
Gauss约束、非局部toron扇区、空间模态重整化
及完整RG源/OS重构均未在齐次MODEL中完成。

## C. 合理的新主线：局部固定物理尺寸块，而非整空间零模

设物理终端块边长a_*~ΛYM^-1，每块有唯一基态、
物理局部激发隙 Δ0>0 的Hamiltonian h_z。
理想无相互作用参考
  H^0_Λ=∑_(z in Λ)(h_z-E0(h_z))
作用于明确的块张量积Hilbert空间，
则谱论严格给出
  gap(H^0_Λ)=min_z gap(h_z)>=Δ0
且与块总数无关。局部excitation本身不是空间零模。

若真实物理终端Hamiltonian可以严格写成
  H^RG_Λ=H^0_Λ+∑_X V_X
并具有某个适用的量子晶格稳定性定理要求的
相对局部形式/范数界，例如
  sup_z ∑_(X contains z) exp(κ diam X)||V_X||
    <=ε_* Δ0
且ε_*是**该定理真实允许的阈值**，
则可能导出uniform gap。
Yarotsky 2004 JMP、2005 J.Stat.Phys、
2006 CMP的弱局部相互作用和相对形式扰动框架
是具有可审计条件的已发表比较路线。
没有证明其技术前提适用于真实SU2 RG终端模型。

该路线仍有四个真实红点：
  (1) 实际Gauss边界约束下的物理Hilbert块空间
      及真空/全中心扇区；简单张量积未获证明；
  (2) 真正的固定物理块Hamiltonian局部谱隙Δ0>0
      且随regulator/volume/RG步数一致；
  (3) 真实RG终端相互作用在适当**局部**
      范数中小，不是全局算子范数小；
  (4) 真实同一OS transfer以及正时间
      Schwinger源字典与对应Hilbert算子的一致性。
这些仍包含非微扰H2的真实难度，
不能把局部模型的谱隙作为I7已得结论。

## D. 裸弱耦合终端稳定性方法的可计算失败

真实3+1D lattice Kogut–Susskind的一种常用归一化为
 H_E=[g²/(2a)]∑_links E_link²,
 H_M=[2/(g²a)]∑_plaquettes [1-(tr U_p)/2].

SU2的最低非零单链路Casimir j(j+1)=3/4，
故单链路电场激发隙
 Δ_el=3g²/(8a).

单个磁相互作用算子范数
 ||V_p||<=4/(g²a)，
因为 -1<=tr(U_p)/2<=1。
3空间维每链路恰在4个空间plaquettes中；
因此逐链路磁源的**粗上界预算**与电场隙之比为
  [4*4/(g²a)]/[3g²/(8a)]
    =128/(3g^4).
数值:
 g=0.5 ->682.6667,
 g=1   ->42.6667,
 g=2   ->2.6667,
 g=3   ->0.52675.

随着裸紫外渐近自由 g(a0)->0，该粗局部扰动比发散。
因此基于裸电场Haar乘积真空作小相互作用
微扰的**这种证书**无法直接控制弱裸耦合；
这是对一种估计上界的失败，并不证明真实模型gap不存在。
需要真正的非微扰 RG 到固定物理尺度后，
再证明适当参考与相互作用的局部稳定性。
在该scale上g_eff未被当前Bałaban old/new-R
证书证明自动进入有隙弱块间作用的区域。

Kogut–Susskind结构可对照
  https://qft.org/lattice-hamiltonian/hamiltonian-lattice-field-theory/lattice-gauge-hamiltonians-gauss-law/
及2025年 E.P.J.C 文献
  https://link.springer.com/article/10.1140/epjc/s10052-025-15120-x .
注意不同Hamiltonian规范化、时间各向异性及
格距因子可能不同，以上所有数值属于显示的模型规范化。

## E. 对旧闭合路线的纠偏

- 第66轮0+1维bosonic SU2量子振子确实有紧预解式，
  但其定量能标无法未经体积归一化转到3+1D。
- 第64轮正算子 q_c+q_f<1 是**充要? 不是**；仅充分，
  该条件可过强，原Schur小交叉更灵活。
- 第65、66轮完整纤维Poincare和粗场H1并不推出H2，
  正时间条件信息泄漏仍未控制。
- 第59、63轮连续体B14同网极限只是抽象逻辑引理，
  不能以改变误差量词代替真实SU2 IR q<1。
- original24 old/new-R两根活动可求和没有证明
  真正的物理终端Hamiltonian可写成局部有隙块和
  小相互作用，也没有给出固定物理时间的实际谱范数界。

## F. 第67轮闭合树——只保留真实动力学承重链

4D SU2 original physical I7
├─ GREEN 历史39/39 CONDITIONAL 依赖保持
├─ GREEN m=3三方向量子振子严格束缚+E0显式夹逼 (纸面)
├─ GREEN 齐次零模物理体积缩放 Δhom∝g^(2/3)/L (模型纸面)
├─ GREEN 局部独立有隙块tensor gap不随volume退化 (抽象纸面)
├─ GREEN 裸弱耦合电/磁局部扰动预算∝g^(-4) (方法审计)
├─ YELLOW 真正物理终端block/Gauss/OS源Hilbert词典
├─ RED 在每个真实固定物理块证明uniform局部gap
├─ RED 在全部真实RG尺度及体积下证明local perturbation smallness
├─ then 适用的gapped quantum lattice stability -> physical q_IR<1
├─ then exact physical OS Gram I7 -> 原主定理 -> 再启动Lean
└─ status: PAPER OPEN, I7 OPEN, NO NEW Lean.

注意：此新的局部块稳定路线同样是**足够条件**，
有可能比原I7本身更强，不能把它当作自动更短路径。
即使成功证明参考块谱隙，也仍需模型侧严格证明
Gauss/边界/局部interaction smallness及整个连续极限；
目前尚未发现能在现有Bałaban证书下闭合这一红点
的非循环推导。

## References (actual papers)

- B. Simon, "Some quantum operators with discrete spectrum but classically continuous spectrum", Ann. Phys. 146 (1983), 209--220. DOI 10.1016/0003-4916(83)90057-X.
- D. A. Yarotsky, "Perturbations of ground states in weakly interacting quantum spin systems", J. Math. Phys. 45 (2004), 2134--2152, DOI 10.1063/1.1705718.
- D. A. Yarotsky, "Uniqueness of the ground state in weak perturbations of non-interacting gapped quantum lattice systems", J. Stat. Phys. 118 (2005), 119--144, DOI 10.1007/s10955-004-8780-x.
- D. A. Yarotsky, "Ground states in relatively bounded quantum perturbations of classical lattice systems", Comm. Math. Phys. 261 (2006), 799--819, DOI 10.1007/s00220-005-1456-9.
- D. Bhattacharjee et al., "One Cube Estimate Implies the Yang--Mills Mass Gap", v7 (2026), https://hexagonmath.org/2610.00341v7: the genuine continuum tuned cube input remains explicitly OPEN.
