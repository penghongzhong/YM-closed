# 第70轮｜原I7纸面主线：桥链路电场精确Casimir、任意规模仙人掌图有隙、三维Bianchi阻断

日期：2026-11-14；研究分支：ym-i7-round70-tree-bridge-bianchi-20261114
承接第69轮：ym-i7-round69-gauge-edge-gluing-20261114

## 0. 严格验收边界
- 历史 39/39 仅 CONDITIONAL（其中I7为显式未证物理输入），未改动。
- 原始4D SU(2) Yang–Mills I7：OPEN；连续体质量隙：OPEN。
- 用户规定“纸面完全闭合才启动Lean”，所以本轮只做数学证明、Published-input核验、无新增Lean、无CI。
- 本轮的“确证”仅适用于**特殊有限图及其任意规模序列**，没有证明它们与3+1D Wilson RG终端谱或OS传递酉等价。

## 1. 精确两环路与桥的 Gauss 商，桥电场Casimir

取两个顶点0,1上的基点自回路 A,B∈SU2，另以桥C∈SU2连接0->1（可视为各自真实四链plaquette缩约后的loop代表）。规范作用是
  A->g0 A g0^{-1},
  C->g0 C g1^{-1},
  B->g1 B g1^{-1}.
记D=CBC^{-1}。规范不变态为
  f(A,C,B)=phi(A,D),
  phi(gAg^{-1},gDg^{-1})=phi(A,D).
因SU2 Haar共轭不变，变量变换(B,C)->(D,C)保Haar，故完全得到
  H_phys ≅ L²(SU2_A×SU2_D)^{Ad_diag}.

设 {-Δ_U} 表示规范化为fundamental Casimir 3/4 的 SU2 bi-invariant Laplacian（对fundamental matrix coefficient作用为3/4）。对桥左电场变化 C->e^{s X_a}C，
  D->e^{s X_a} D e^{-s X_a}.
在缩约坐标中，桥电场的非负Casimir为
  K_C=-Σ_(a=1)^3 J_(D,a)^2 >=0,
  J_(D,a)phi(A,D)
   = d/ds|_{0}phi(A,e^{s X_a}De^{-s X_a}).

因此对所有光滑共同共轭不变量，
  (−Δ_C)f  ↔ K_C phi.
对两个loop各自的全四条环路原始link electric sum，
每条边根据bi-invariance都贡献同一个−Δ_(A or D)，
所以**plaquette-decorated** two-loop-with-bridge图的纯电能为
  H_E=(g²/(2a))[4(−Δ_A−Δ_D)+K_C].
这里的K_C不是零，也不是一个在大体积下可随意丢弃的微小电荷修正。

取第69轮真实混合Wilson源
  F(A,D)=tr(AD)−(1/2)trA trD
        =−2 \vec a·\vec d.
它是固定A情况下的D-conjugation spin-1矩阵系数，
所以
  K_C F=1(1+1)F=2F.
而
  (−Δ_A−Δ_D)F=(3/2)F.
故
  [4(−Δ_A−Δ_D)+K_C]F=8F,
  H_E F=(4g²/a)F.
但 separately class-invariant component
  G(A,D)=(1/2)tr A tr D
满足 K_C G=0 与
  H_E G=(3g²/a)G.
并且正如第69轮，
  ||F||²_(Haar×Haar)=3/4,
  ||G||²=1/4,  ||tr(AD)||²=1.

因此桥 electric term 对被遗漏的75%界面源
给予**精确的正电场能罚 g²/a**。这是同一个
真实有限图 Kogut–Susskind 电场拉普拉斯算子的结果，
不是凭空添加的罚能。

该机制有局限：磁势V_B、外部相互作用及
更复杂格点上的共享链路可能改变全Hamiltonian
的谱排序，不能从一个测试源的电场能量直接推导
真实无限体积质量隙。

## 2. NEW 严格纸面定理：任意多个 SU2 plaquette 装饰树的完整KS gap不随规模退化

定义特殊3D空间的有限**仙人掌/cactus** graph:
  T=(V_T,E_T) 为任何有限有根树；
  每个树顶点z附着一个四边形plaquette环路，
  四边形仅在其基点与T相交；
  不同plaquette之间没有共享边、没有跨块磁plaquette。
每个桥e∈E_T为原始一条 link，但不在任何plaquette中。

这是一个真实 SU2 pure-gauge Kogut–Susskind Hamiltonian
作用于此图的规范不变Hilbert，而不是简单的
局部 class function tensor product。
先按各plaquette的三个非基点Gauss变量固定其内部
三条tree links，留下独立loop variables U_z∈SU2；
再用T作最大树固定所有桥links，剩余root的
同时共轭Gauss不变条件是
  H_phys ≅ L²(SU2^{V_T})^{Ad_diag}.

精确缩约电场形式为
  H_E=(g²/(2a))[
       4 Σ_(z∈V_T)(−Δ_(U_z))
       + Σ_(e∈E_T)K_e ],
其中 K_e≥0 为桥左电场的平方Casimir：
  K_e=−Σ_(α=1)^3(
       Σ_(z in Desc(e))J_(z,α))².
这里Desc(e)为从root看穿过该桥后整棵
子树的全部loops；J_(z,α)为对U_z的
共轭微分生成元。每个J反自伴，所以K_e≥0。

真实bare磁项只有每块各自的初等plaquette：
  H_M=[2/(g²a)]Σ_z(1−tr(U_z)/2).

因此 EXACTLY
  H_T = H0 + K_bridge,
  H0 = Σ_z h_g(U_z),
  h_g(U)= [2g²/a](−Δ_U)
             +[2/(g²a)](1−trU/2),
  K_bridge=[g²/(2a)]Σ_e K_e ≥0.

各单块h_g是在**FULL SU2 L²空间**上的
紧群椭圆Schrödinger算子；唯一严格正基态
ψ_g(U)>0，因h_g中心对称而是class function。
记e0(g,a)与Δ_full(g,a)>0为各单块
基态能量及其**FULL SU2非真空**谱隙。
注意Δ_full不一定等于Round68只在class
物理子空间所算的Δ_class；在弱耦合端
前者可因spin-1 first-oscillator而更小。

product Ω_T=⊗_z ψ_g(U_z)同时是H0的
唯一归一基态，并在root共轭下物理不变。
更强：对每个z及α，J_(z,α)ψ_g=0，
所以 K_e Ω_T=0 对所有桥成立。
因而
  H_T Ω_T = |V_T| e0 Ω_T,
且 H_T≥H0≥|V_T|e0+Δ_full(g,a)(I−P_Ω).
结合Ω的显式本征值，这就是整个扩展
和完整Gauss物理非真空子空间的谱隙下界：
  ***gap(H_T|H_phys) >= Δ_full(g,a)>0***
对任意树形、任意plaquette块数、任意体积严格成立。
没有使用Yarotsky弱相互作用小参数；
桥的规范电场耦合本身可能很强，只因其
为非负Casimir且精确湮灭class-product ground，
而不关闭gap。

这个特殊图系列属于真正紧群SU2 KS
Hamiltonian，因此是比Round69任意规模
“强耦合回路toy”更接近实物的纸面正结果。
然而它没有格点三维体胞/相邻面共享边，
无法逼近完整3+1D YM。不能称作Clay I7解决。

可以对每个固定g>0取统一物理下界。
如果需要g在任意紧正区间变化，
单块full SU2椭圆谱随参数连续且基态唯一，
故 inf_(g∈[gmin,gmax])Δ_full(g,a)>0
（同一a固定或统一物理a_*限制）。
完全所有g>0的统一dimensionless gap
还可以通过3D谐振子弱耦合
Δ_full(g,1)->sqrt2 与强耦合
Δ_full(g,1)~3g²/2来论证，
但这需要明确调用标准紧流形半经典
低能谱极限定理；本轮主结论不依赖这一步。

## 3. EXACT 真正3D cubic graph中的广延Bianchi阻断

对开边界 L×L×L 立方晶胞，顶点数、link数、
初等plaquette数和立方胞元数恰为
  N_V=(L+1)^3,
  N_E=3L(L+1)^2,
  N_P=3L²(L+1),
  N_C=L³.

有限连通graph在最大树规约后独立闭环link数
  r=N_E−N_V+1=2L³+3L².
而
  N_P−r=N_C=L³,
所以
  N_E−N_V+1=N_P−N_C.                  (70.1)

数值:
  L=1: r=5, P=6, C=1;
  L=2: r=28,P=36,C=8;
  L=4: r=176,P=240,C=64;
  L=8: r=1216,P=1728,C=512;
  L=16:r=8960,P=13056,C=4096.
C/P=L/[3(L+1)]->1/3.

这一差值不是一个可忽略的表面修正，
而是空间体积广延的Bianchi链关系。
在每个3D elementary cube，六个面
plaquette holonomy经合适平行移动到同一基点，
按规定次序相乘严格为SU2单位元。
在单位元附近线性化后，约束Jacobian秩
为每个立方胞元3个Lie代数分量（开边界
simply connected cell complex的\partial_3无核），
所以rank(P−r)=N_C个group-valued relations.

更直接，对于单一立方胞元：假设把六个face
holonomies误建模为6个独立Haar SU2变量，
其nonabelian Bianchi relation
  OrderedProduct(transports, U_face)=I
要求最后一个face取唯一的其它五个face
所决定的逆元素。因SU2 Haar无原子，
这个约束集合在product Haar下测度零。
但真实link-Haar pushforward (以及任何
严格正有限g Wilson link Gibbs推前)的face
holonomies满足真实Bianchi恒等式，几乎
处处落在此集合。
因此 **真实face律对naive全独立face-Haar乘积律
是奇异的**；不能靠一致有界的Gibbs密度比
或“小有界磁势扰动”把一个变成另一个。
这个奇异性是选用P个独立face变量的后果，
不是宣称真实Wilson link变量与本身Haar
测度奇异（后者有限cutoff下反而有
严格正密度）。

这指出从仙人掌图向真实三维cubic网格推广时
的一个精确红点：需要保留
**Bianchi硬约束和共享边的几何**，
不能只给每个单plaquette rotor加几个
范数很小的V_X。

## 4. 若用独立基本loop变量避开Bianchi，则电场变为非局部

对真正连通cubic网格，最大树规约保留r=N_E−N_V+1
个独立fundamental cycle/chord SU2变量；
这是合法、正确的独立Haar坐标（只剩root
global Ad约束），不存在对r变量的
face-Bianchi硬约束。

但每条被最大树删除的电场link
在这些loop坐标中变为**沿该tree link
穿过的全部fundamental loops的
左/右 Lie algebra生成元之和的平方**。
这是物理Kogut–Susskind电场的精确
非阿贝尔表达，而不是一个小的局部扰动。
参考:
 D'Andrea–Bauer–Grabowska–Freytsis,
 "New basis for Hamiltonian SU(2) simulations,"
 Phys.Rev.D109 (2024) 074501,
 DOI 10.1103/PhysRevD.109.074501,
 Appendix C and Eq.(119);
 以及Carena–Lamm–Li–Liu,
 "Quantum error thresholds for gauge-redundant
 digitizations of lattice field theories",
 Phys.Rev.D110 (2024) 054516,
 DOI 10.1103/PhysRevD.110.054516.
这两篇公开文章都明确指出
最大树规范固定一般使电场Hamiltonian非局部。

可在具体合法最大树上定量看到规模损失。
将L×L×L开盒沿某一x方向固定平面切为
两块互相连通的子立方格子，在两侧
各选一棵spanning tree，只用跨平面的
一条link t连接两侧，构造合法全域tree。
跨平面的原图link共有(L+1)²条，
其中tree仅包含t，其余
  M=(L+1)²−1
条均是独立chord。
这些chord的fundamental cycle都经过t，
所以t的电场
  K_t=(Σ_(κ in crossing chords) J_κ + …)²
含M=Theta(L²)个非阿贝尔电场生成元，
展开有O(L^4)个chord-pair二阶耦合项
（加上具体左/右方向符号和其他变量）。
K_t仍为非负算子；**不能因其正性
就把它当作规范局部的范数小扰动**。
该明确tree选择已经说明简单的
independent-loop+uniform local norm模型
与真实cubic-electric结构并不一致。
并未证明所有可能规约/坐标下的
相互作用都必须同样非局部。

## 5. 与原I7最短链的严格对应，及剩余单一红点

第69轮的
  1. 边界Wilson源F的75%投影损失；
  2. extended-Hilbert先证gap再Gauss投影；
  3. 多loop strong-g stable toy
都是合理的特殊参考。

本轮进一步给出：
  🟢 真实bare SU2 Kogut--Susskind在任意多块
      cactus graph上即使存在Gauss桥电场
      仍有严格统一gap，完全不用假设
      bridge作用小；
  🟢 真正三维cubic：face变量若全部独立，
      Bianchi使其真实law相对乘积Haar奇异；
  🟢 独立fundamental loop坐标虽避开Bianchi，
      tree-electric则含真实非局部电场项，
      在一合法tree上有Theta(L²) loop耦合；
  🟡 需要建立同时保留Gauss/Bianchi/OS
      的终端物理块变量及local form表示；
  🔴 证明完整真实4D SU2物理终端effective
      Hamiltonian具有体积/UV/所有物理
      扇区一致的正spectral margin，而
      当前old/new-R只控制部分UV聚合物
      没有给出该H2生产者。

本轮严格纸面结果不含新的无条件4D
mass gap，也没有任何原I7的真实
q<1证书。不能把cactus graph的
uniform gap移植到cubic continuum时
忽略Bianchi和树规范电场的代价。

**I7 PAPER OPEN；按用户要求 NO LEAN。**
