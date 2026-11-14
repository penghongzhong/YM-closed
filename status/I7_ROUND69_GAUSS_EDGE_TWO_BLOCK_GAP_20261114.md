# 第69轮｜I7 一小时集中纸面攻关：SU(2) 边界拼接、精确界面源、双块相互作用谱隙

Date: 2026-11-14
Branch: ym-i7-round69-gauge-edge-gluing-20261114
Parent: ym-i7-round68-compact-block-gap-20261114

**验收：物理 I7 OPEN；历史39/39仅CONDITIONAL。遵循用户“纸面尚未闭合不启动 Lean”的指示，本轮不新建Lean、不运行CI、不修改原条件性主分支。以下只有明示的有限图/抽象 Hilbert 定理闭合，绝无四维无限体积/连续体质量隙证明。**

## A. 两个 plaquette 在基点拼接：Gauss 的相对取向扇区

考虑仅在一个基点相交的两条闭合 SU(2) plaquette loops，按生成树固定其余顶点的规范自由度，剩余基点同时共轭：
  (A,B) -> (gAg^{-1},gBg^{-1}).

正确的规范不变 kinematic Hilbert 为
  H_glued = L²(SU(2)², dHaar_A dHaar_B)^{Ad_diag}.
如果先分别对每个环路施加共轭不变性，则
  H_sep = L²(SU(2))^{Ad} ⊗ L²(SU(2))^{Ad}
是 H_glued 的真闭子空间，少了跨边界相对取向激发。

利用 SU2 作为单位四元数 S³：
  A=a0 I+i a·σ, B=b0 I+i b·σ,
  a0²+|a|²=b0²+|b|²=1.
可取 Pauli 符号使
  tr A=2a0, tr B=2b0,
  tr(AB)=2(a0 b0-a·b).

令
  F(A,B)=tr(AB)-0.5 tr A tr B=-2a·b.
F 在共同共轭下不变，但不是分别共轭不变。

对于独立归一 Haar，条件于a0,b0两向量a,b的
角度独立且均匀分布于S²（给定长度）。
由 E_Haar(a_i²)=1/4 和 E(a_i a_j)=δ_ij/4：
  E(F|tr A,tr B)=0,
  ||F||²=4 Σ_i E(a_i²) E(b_i²)=4*3/16=3/4.

因为 AB 也服从 Haar，
  ||tr(AB)||²=E[(tr AB)²]=1.
正确的独立共轭条件投影 P_sep 满足
  P_sep tr(AB)=0.5 tr A tr B,
  ||P_sep tr(AB)||²=1/4,
  ||(I-P_sep) tr(AB)||²=3/4.                   (69.4)

故在此完全可解的真实SU2有限图上，
“把两块的单独规范不变代数作张量积”
漏掉混合 Wilson 源75%的 Haar L² 范数平方。
该丢失不是高表示的假象。

在 H_E=-Δ_A-Δ_B（每个SU2群上 Casimir 归一
(-Δ)trU=(3/4)trU）下，
  H_E F=(3/2)F,
  H_E [0.5 trA trB]=(3/2)[0.5trA trB].
因此两部分都在同一个有限电场能级，
不会因这一简单电场演化而自动实现
  ||(I-P_sep)F||² ->0.

特别强调：这里的 P_sep 是 **Haar kinematic L² 投影**，
尚未构成实际4D SU2欧氏OS Hilbert的粗场投影。
此例是规范拼接/源空间的严格反例，
不代表真实时空Wilson正时间协方差的值。

### 接到已经严格Lean通过的 Wilson根代数

已验收原代码
  YMOriginal/OriginalI7_MandelstamWilsonRoot.lean
  YMOriginal/OriginalI7_MandelstamSU2.lean
严格证明
  trA trB=tr(AB)+tr(AB^{-1}),
  wilsonRoot(U)=2-trU (SU2 trace real).
故
  F(A,B)=0.5[tr(AB)-tr(AB^{-1})]
         =0.5[W(AB^{-1})-W(AB)].              (69.13)
F不是额外引入的source类型：它是两条真实
以同基点为基的Wilson环路的线性组合。
尤其它可由**局部可缩**的两个loop拼接而得，
无需全环面的非可缩toron模式。
前Round55的all-based-loop家族可容纳F，
但仅有每块内部的Wilson class家族不能。

### Peter--Weyl 边界扇区的准确表示

各块在独立边界共轭 SU2 作用下分别分解
  H_A=directsum_{l>=0} V_l ⊗ M_{A,l},
  H_B=directsum_{l>=0} V_l^* ⊗ M_{B,l},
这里 l 是整数非负的SU2共轭作用自旋，
并非左/右regular SU2的半整数j；
中心对共轭作用平凡。对角Gauss不变空间为
  (H_A⊗H_B)^{SU2}
     ~= directsum_{l>=0} M_{A,l}⊗M_{B,l}
（每个V_l⊗V_l^*中配对一个不变张量）。
各块先投影Gauss单态只保留l=0一项。
F正是l=1(Ad)边界表示配对得到的singlet。
其能量3/2来自矩阵系数在左/右 SU2
regular Laplacian下的fundamental Casimir3/4，
与边界共轭扇区标签l=1没有矛盾。

## B. 完整扩展Hilbert到物理Gauss子空间的 gap 保存定理（纸面严格闭合）

设 compact gauge group G 在扩展Hilbert H_ext上
以幺正表示 U(g)作用；P_G=∫_G U(g) dg
是H_phys=H_ext^G的正交投影。
设自伴 H_ext 与全部U(g)对易，且有唯一
规范不变基态Ω、基态能量E0，并已证明
  H_ext-E0 >=Δ (I-|Ω><Ω|), Δ>0
为二次型不等式。
由于P_G Ω=Ω且H_ext约化H_phys，
对任意ψ∈H_phys∩Ω^perp，
  <ψ,(H_phys-E0)ψ>
   =<ψ,(H_ext-E0)ψ>
   >=Δ||ψ||².
故
  gap(H_phys)>=gap(H_ext)>=Δ.             (69.5)

这是Gauss拼接的可行修复：保留边界charge
表示与完整扩展tensor product，先有隙，
最后实施Gauss投影。
但是对H_ext全部带电扇区证明有隙，
可能严格强于物理I7。
精确SU2反例：
  H_ext = trivial ⊕ V_(1/2) ⊕ trivial,
  H_eps =diag(0, eps I_2,1).
扩展gap=eps->0，而Gauss物理
invariant子空间gap=1。
所以这一修复是SUFFICIENT，不是
必要；也不能把任何扩展Hilbert gap
当成可免费取得的Yang--Mills物理输入。

## C. 非零跨块Wilson相互作用仍有隙：显式耦合区间（新有限模型定理）

在扩展 kinematic L²(SU2²) 上设置
  h_g(A) = (2g²/a)(-Δ_A)
            +(2/(g² a))(1-0.5 tr A),
  H_AB=h_g(A)+h_g(B)
        +(2/(g² a))(1-0.5 tr(AB)).
这可视为两块各有基本plaquette Wilson势，
外加跨两环的复合Wilson回路项。
整个模型在共同共轭下SU2规范不变，
并保留前述边界界面态。
但 tr(AB) 是跨块COMPOSITE LOOP，
不是四维裸Wilson作用的一片新的
elementary plaquette。RG effective action可能
产生这类项，但本轮没有证明其真实RG系数。

SU2 round S³的Casimir first nonzero eigenvalue
  λ1(-Δ_SU2)=3/4.
故自由扩展单块电场隙=3g²/(2a)。
单块磁势V_A>=0，且常数Haar试探态
磁能期望正好2/(g²a)。
由minmax，
  Δ_g:=gap(h_g)
     >=(1/a)(1.5g²-2/g²).                 (C1)

由于 h_g 是紧连通群上的椭圆实
Schrödinger operator，groundψ_g unique,
strictly positive and conjugation invariant。
其ground-state measure ψ_g²dH为中心律，
  E_{\psi_g²}(A)=m_g I, m_g∈[-1,1].
两个独立ground的跨块Wilson势期望
  E_Ω V_cross
   =(2/(g²a))(1-E trAB/2)
   =(2/(g²a))(1-m_g²)
   <=2/(g²a).

令H0=h_g(A)+h_g(B)，ground energy=2e0，
gap至少Δ_g；V_cross>=0，
故E1(H_AB)>=2e0+Δ_g。
用Ω=ψ_g⊗ψ_g试探E0，
  E0(H_AB)
   <=2e0+(2/(g²a))(1-m_g²).
两式严格推出
  gap(H_AB)
   >=Δ_g-(2/(g²a))(1-m_g²)
   >=(1/a)(1.5g²-4/g²).                  (69.7)

若 g⁴>8/3 (=2.6667)，则正且显式。
g阈值 (8/3)^(1/4)=1.2778862084925449。
举例 a=1：
  g=1.3: gap>=0.16813609,
  g=1.5: gap>=1.59722222,
  g=2.0: gap>=5,
  g=3.0: gap>=13.05555556.

H_AB全扩展Hilbert的ground唯一且
common-conjugation invariant，按B节投影
后，物理Gauss子空间的谱隙不小于上述
扩展模型的严格正下界。

这确实把Round68的isolated块推进成
**一个有相互作用的Gauss不变双块模型**。
但没有证明任意块数的spectral gap统一，
更没有证明真实4D SU2 RG终端Hamiltonian
与这一H_AB相同或小扰动等价。

## D. 两块模型的小耦合端：标准半经典孤立势阱方法（纸面）

对 a=1，写h=g²并令
  W(A,B)=2[(1-tr A/2)+(1-tr B/2)
                  +(1-tr(AB)/2)]>=0.
则
  h H_AB= -(h²/2)(Δ_(S³,A)+Δ_(S³,B))+W(A,B).

W唯一零点是A=B=I。
在该点附近取单位四元数向量坐标
A=(sqrt(1-|x|²),x), B=(sqrt(1-|y|²),y)：
  W(x,y)=|x|²+|y|²+|x+y|²+O((|x|+|y|)^4)
（在多项式展开中存在三次/四次项，但不影响正Hessian；
局部等号的 O(x^4) 若含非零三次项应改为 O(x^3)；
严格使用 W=quadratic+O((|x|+|y|)^3)，见下一句）。
精确需要仅
  W(x,y)=|x|²+|y|²+|x+y|²
               +O((|x|+|y|)^3),
其Hessian严格正定。
SU2 round Laplacian下动能局部为
  -(h²/2)(Δ_x+Δ_y)+lower-order metric terms.

按x=gξ,y=gη缩放，物理aH_AB
的低能形式趋于
  H_osc=-1/2(Δ_ξ+Δ_η)
                +|ξ|²+|η|²+|ξ+η|².
在ξ_±=(ξ±η)/sqrt2变量中，
  H_osc=-1/2(Δ_++Δ_-)+3|ξ_+|²+|ξ_-|².
所以频率ω_+=sqrt6, ω_-=sqrt2。
可调用标准紧流形上**唯一非退化势阱**
Schrödinger半经典低能谱收敛定理
（或用IMS+变分上下界直接建立）：
  lim_(g->0) gap(H_AB on full ext)=sqrt2/a.

物理同时共轭作用在ξ±上
为共同SO3旋转；单振子一量子态
变换为向量，而非singlet。
首个非零旋转singlet激发可以由
两个ω_-的量子组成（径向 l=0），
其代价2ω_-=2sqrt2。
其它混合l=1×l=1 singlet能级
>=ω_-+ω_+>2ω_-。
因此
  lim_(g->0) gap(H_AB on phys)=2sqrt2/a.    (69.10)

大g时电场项支配，有限块全gap
至少(1.5g²-4/g²)/a->infinity。
在每个固定g>0，H_AB为紧连通
SU2²上的正性改进椭圆Schrödinger
operator，ground唯一，谱离散，
并随g norm-resolvent continuous
（共同椭圆域＋有界参数连续势）。
所以 gap_phys(g)>0，连续，
两端皆有正下界，得到
  exists δ_AB>0:
    inf_(g>0) [a*gap_phys(g,a)] >=δ_AB.     (69.11)

这一论证对标准半经典低能谱收敛及
群约束扇区谱收敛的调用必须作为
公开的数学输入陈列；它不是
Lean检查过的全g数值区间证书。
实质仍只有**固定两个块**的严格paper model gap。

## E. 重整化混合源的弱耦合范数并不自动消失

对两块分别独立的h_g groundψ_g⊗ψ_g，
弱g的每块谐振子极限为
  H_one,osc=-1/2 Δ_ξ+|ξ|².
基态概率下每坐标 Varξ_i=1/(2sqrt2)。
前述 F=-2a·b，在A≈exp(i g ξ·σ),
B≈exp(i g η·σ)下有
  g^(-2) F(A,B)->-2 ξ·η.

独立极限Gaussian下严格得到
  lim_(g->0) E|g^(-2)F|²
    =4 Σ_i Varξ_i Varη_i
    =4*3*(1/(2sqrt2))²=3/2.             (69.12)
由于每个h_g ground保持共轭不变，
F对两个块分别class-measurable代数
的投影恒为0（逐g成立）。
所以即使各A,B->I，正确缩放后的
低阶混合Wilson源仍可有O(1)范数。

这是**独立两块参考模型**的定理，
不等于完整有相互作用H_AB ground、
也不是实际4D连续体曲率重整化定理。

## F. 任意块数最关键的稳定性难题：广延真空移位

设B个独立局部h_z参考块，每块gap>=Δ0，
  H0=Σ_z h_z.
如果只知道每条跨块Wilson势V_e>=0，
||V_e||<=J（常数与体积无关），
则minmax仅给出
  E1(H0+Σ_eV_e)>=E0(H0)+Δ0,
而试探product ground给
  E0(H0+Σ_eV_e)
    <=E0(H0)+Σ_e<Ω0,V_eΩ0>
    <=E0(H0)+J |E_graph|.
于是粗差分下界
  gap(H)>=Δ0-J|E_graph|，
对|Λ|->infinity必然无效。
对于本轮真实SU2双块势，
Ω0正性与V_cross非零保证
  <Ω0,V_crossΩ0>
    =(2/(g²a))(1-m_g²)>0
（有限g时ψ_g处处正，所以|m_g|<1）。
故跨块交互并非frustration-free
且不能靠单纯V>=0保存参考gap。

若某个理想模型的相互作用
V>=0且VΩ0=0，确有简单uniform gap，
但它不适用于当前Wilson跨块势。
必须构造真正DRESSED interacting vacuum
及局部相互作用稳定性，才能消除
体积广延的ground-energy shift。

已发表Yarotsky结果针对弱局部/相对形式
扰动的gapped product/reference models有结论：
- D. Yarotsky, J.Math.Phys.45 (2004) 2134–2152
  DOI 10.1063/1.1705718.
- D. Yarotsky, Comm.Math.Phys.261 (2006) 799–819,
  DOI 10.1007/s00220-005-1456-9.
本轮**没有**推出真实SU2
H_eff=Σh_z+Σ_XV_X的exact OS/Hamiltonian字典，
也**没有**证明真实terminal effective
||V||_local/Δ0低于任何定理允许的门槛。
Bałaban U1 old/new-R活动小性只能
控制部分欧氏聚合物，不能自动当成
全部物理Hamiltonian V_X的局部相对范数。

## G. 原I7的最短承重红点（而非新辅助定理清单）

**逻辑上已闭合（纸面/已承接旧Lean）：**
- 实际有限图 SU2 mixed loop grammar（旧Mandelstam Lean已证）。
- 界面边界 SU2 conjugation/edge mode 必须保留，精确有75% Haar范数丢失。
- 有隙extended Hilbert经Gauss投影仍有隙。
- 具有跨块Wilson作用的**固定两个块**模型在g^4>8/3显式有隙，标准半经典补全其所有g>0的有限模型gap。
- 若真实终端多块模型落入适用的Yarotsky稳定区域，
  全空间 uniform gap经OS字典可推出I7。

**原物理模型依然完全未闭合：**
1. 从完整四维SU2 Wilson RG（包括IR Gaussian和大场）
   构造与原Original15相同物理OS transfer/Hamiltonian的
   exact boundary-extended block Hamiltonian dictionary。
2. 在该真实terminal Hilbert中构造所有边界charge/toron
   物理扇区，并证明需要的uniform block gap。
3. 证明所有真实跨块及长程V_X的local norm/relative
   form小于published stability threshold，独立于
   regulator/volume/exhaustion和紫外层数。
4. 在同一原始物理窗口/时标下传回全体complex
   centered Wilson Gram I7，不遗漏F等mixed sources。

目前没有数学证明将现有old/new-R 输入升级
为1--4；以上固定两块的实验室结果不构成
任意块数的uniform gap，也没有解除I7。

历史39/39仍CONDITIONAL，I7 PAPER OPEN，
遵守用户要求：**未启动Lean、未添加Lean环境**。
Clay数学研究所仍列该问题UNSOLVED。

## H. 正式参考与辨析

- Forni–Goldman–Lawton–Matheus, "Non-ergodicity on SU(2)
  and SU(3) character varieties of the once-punctured torus,"
  Annales Henri Lebesgue 7 (2024), 1099–1130, DOI 10.5802/ahl.216,
  Sec 2.2: SU2 rank-2 trace invariants tr A,tr B,tr AB.
- Donnelly–Freidel, "Local subsystems in gauge theory and gravity,"
  JHEP09 (2016) 102, DOI 10.1007/JHEP09(2016)102:
  boundary edge modes and nonfactorization by Gauss law.
- Yarotsky 2004/2006 citations above; theorem assumptions must
  be checked for the real YM RG terminal model.
- Clay CMI official Yang–Mills & the Mass Gap status remains unsolved,
  https://www.claymath.org/millennium/yang-mills-the-maths-gap/.
