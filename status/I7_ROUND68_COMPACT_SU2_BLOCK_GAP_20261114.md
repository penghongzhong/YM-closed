# 第68轮｜I7纸面证明：真实紧群 SU(2) 有限规范块谱隙与块间红点

日期：2026-11-14
研究分支：ym-i7-round68-compact-block-gap-20261114
继承：ym-i7-round67-matrix-volume-20261114
真实原物理 I7：**OPEN**
历史原主链 39/39：**CONDITIONAL**，其显式 I7 等假设未解除。
本轮不新增 Lean 定理或 CI（遵守纸面闭合优先），不宣称解决四维 Yang–Mills。

## 1. 一块真正满足 Gauss 约束的 SU(2) plaquette

取一张由四条独立有向链路构成的方形图，局部
Gauge group \mathcal G=SU(2)^4 作用于 L²(SU(2)^4)。
其规范不变 Hilbert 空间与 SU(2) 共轭类函数的
L² 空间酉同构：固定生成树后只剩回路乘积
  U=U_1 U_2 U_3^(-1) U_4^(-1)
和在基点的共轭作用。

取单块 KS Hamiltonian（a 是这一块的实际格距）
  H_\square(g,a) =
    (g²/(2a)) Σ_(ell=1)^4 E_ell²
    +(2/(g²a))(1-tr U/2),  g>0.
这里 E_ell² 的 SU(2) Casimir 对自旋 j 的值为 j(j+1)。

由规范不变正交角色 χ_j(U)，j=0,1/2,1,...，
  Σ E_ell² χ_j=4j(j+1)χ_j;
  χ_(1/2)χ_j=χ_(j+1/2)+χ_(j-1/2),
且 χ_(-1/2)=0。

令 n=2j=0,1,2,...，则完整、无限阶的精确
Jacobi 表示为
  H_nn = (g²/(2a))n(n+2)+2/(g²a),
  H_(n,n+1)=H_(n+1,n)=−1/(g²a),
其它非对角元为0。                   (68.1)

在共轭角 θ∈[0,π] 下，
χ_(n/2)(θ)=sin((n+1)θ)/sinθ，
Haar 类测度为 (2/π)sin²θ dθ。
酉变换 f->sqrt(2/π)sinθ f 后，得到
  H_\square ≅
    (g²/(2a))(-d²/dθ²−1)
     +(2/(g²a))(1−cosθ)
在 L²((0,π),dθ) 且 u(0)=u(π)=0。      (68.2)

这是定义清楚的真实紧群单 plaquette 规范约束
Hamiltonian，不是第66–67轮非紧 R³ 向量矩阵模型。
一维 regular Dirichlet Sturm–Liouville 理论保证
紧预解式、第一与第二本征值简单，
  Δ_\square(g,a):=E1−E0>0
对每个固定的 g>0、a>0 都成立。

## 2. 显式单块谱隙下界（纸面闭合）

在规范不变角色子空间，
无磁势的电场算子第一激发能为
  E1(H_el)=4*(3/4)*g²/(2a)=3g²/(2a).
磁势 V=(2/(g²a))(1−tr U/2)≥0，
故 min-max 给出 E1(H_\square)≥3g²/(2a)。

以常数归一角色 χ0=1 试探，
  <χ0,Vχ0>=(2/(g²a))(1−E_Haar tr U/2)
          =2/(g²a),
因为非平凡角色 Haar 均值为0。
所以 E0(H_\square)≤2/(g²a)。
两式相减得到
  Δ_\square(g,a)
     ≥ [3g²/2−2/g²]/a.                (68.4)
只要 g^4>4/3，这个完全显式的下界严格正。
其余 g 的严格正性仍由 Sturm–Liouville 保证，
不是式(68.4)失效就说明 gap=0。

## 3. 弱、强耦合极限及单 plaquette 的全正耦合统一下界

取 a=1 并作 θ=gx，使区间变为 (0,π/g)：
  H_g=−0.5 d²/dx²−0.5g²
     +(2/g²)(1−cos(gx)).
在 0≤gx≤π，
  (4/π²)x² ≤(2/g²)(1−cos(gx))≤x².
系数局部趋于 x²，而上面的二次势下界
保证任意固定低能级的紧性和无逃逸，
由变分形式收敛得到半直线 Dirichlet 振子
  H_0=−0.5 d²/dx² +x², x>0, u(0)=0。
其本征值是全线谐振子的奇宇称能级
  E_k(H_0)=(2k+3/2)*sqrt(2), k≥0，
所以
  lim_(g↓0) Δ_\square(g,1)=2sqrt(2).    (68.8)

另一方面 0≤V≤4/g²，且H_el的前两能级
为0与(3/2)g²，minmax给出
  Δ_\square(g,1)=(3/2)g²+O(g^(-2))
as g->infinity。

所有正耦合上两条本征值随g连续且简单，
小g、大g两端的 gap 都远离0，
由紧区间极小值存在性得到
  exists δ_\square>0:
   Δ_\square(g,a)≥δ_\square/a for ALL g>0.  (68.9)

这是一个严格的、没有显式最佳δ常数的
**孤立单 plaquette** 结论；
不能直接推广到完整时空 SU2 Wilson RG 终端。

## 4. 精确整数 Sturm + 无穷尾解析区间认证

Research script:
  research/i7_round68_exact_single_plaquette_sturm.py

取g=p/q(正有理)，N=1000，
以 n=0,...,N−1 的角色基截断得到J_N。
整数倍 M=(2p²q²*10^6)J_N，
在阈值 k/10^6 的整数 leading principal
determinants 使用三项递推
  D_0=1, D_1=a_0,
  D_(n+1)=a_n D_n−b²D_(n−1)
进行 **精确整数** 符号变化次数计算，
定位J_N的前两个特征值到10^(-6)区间，
无浮点误判。

无限 Jacobi 算子的末端 n≥N 主块 D 满足
  D≥m I,  m=g² N(N+2)/2.
其与J_N的唯一耦合大小为 c=g^(-2)。
对任意截断 x 和尾向量 y，
Young 不等式控制
  2Re <x,C y>≥
    −(2c²/m)||x_(N−1)||²−(m/2)||y||².
故
  H_\infty≥(J_N−δ P_(N−1))⊕(m/2)I,
  δ=2c²/m=4/[g^6 N(N+2)].
若 m/2>λ1(J_N)，由minmax与Rayleigh–Ritz
得对k=0,1：
  λ_k(J_N)−δ≤λ_k(H_\infty)≤λ_k(J_N).
因此真实全角色无限Jacobi的谱隙在
  [gap(J_N)−δ,gap(J_N)+δ] 内。

脚本使用准确的整数阈值/Sturm符号变化
和有理数δ，已完成四组校验。
a=1的经过外扩四舍五入的安全区间：
  g=0.5 : 2.66393451 < gap < 2.66444749
  g=1   : 2.19648100 < gap < 2.19649100
  g=1.5 : 3.45569064 < gap < 3.45569336
  g=2   : 6.01455993 < gap < 6.01456207.
这些是 **单块Hamiltonian的数学证书**，
不是对真实4D空间无限体积质量隙的认证。
对 g=1.5 需保留该行的小数外扩区间，
不要把几位数字的近似值写成精确本征值。

## 5. 固定有限 SU2 规范块，任意外边界、紧耦合区间

更一般，固定有限连通图B，内部链路数E固定，
外边界链路数也固定。设在SU2^E上
  H_(B,eta,g) = κ(g) Σ_(e∈B)(−Δ_e) + V_(eta,g)(U)
为椭圆 Schrödinger/KS operator，
κ(g)>0，V为有界实连续Wilson plaquette磁势，
所有外边界eta属于紧空间SU2^{E_boundary}，
g处于固定正紧区间[gmin,gmax]。

紧连通流形上该算子紧预解式，其热半群正性
改进，故最低本征值简单，基态h_(eta,g)>0。
如果H与内部允许的规范变换对易，该唯一
正基态本身规范不变，物理Gauss子空间的
激发谱隙不小于全Hilbert空间的谱隙。

对ground-state变换可严格导出
  <h f,(H−E0)h f>
    =κ(g)∫Σ_e|∇_e f|² h² dHaar^E.
Haar-Poincare恒等式 λ1(Σ−Δ_e)=3/4，
故
  Δ_B(eta,g)
   ≥(3/4)κ(g)
      [min_U h_(eta,g)(U)² / max_U h_(eta,g)(U)²] >0.
连续依赖于有限边界及紧耦合参数，
可对eta,g取统一正的δ_B( compact g interval)。

这真正完成了**固定有限紧群KS块本身**的
局部有隙性证明，不需要非紧交换子
量子振子的类比。

IMPORTANT: 当前真实YM RG终端块一般有
跨尺度非局部有效相互作用/非标准时间核，
尚未证明可确切写成上述固定E、固定κ、
有界Wilson plaquette磁势的自伴Hilbert算子。
因此这个模型定理并不解除I7本身的H2红点。

## 6. 新精确反例：唯一局部有隙真空+有限程有界相互作用，
## 整体仍可能出现L^-2谱隙

每个局部量子比特定义
  h_i =|down_i><down_i|,
孤立块的唯一基态是up，gap=1。
取N≥2及固定J>0，
定义最近邻置换S_(i,i+1)，
  H_N=h_1+JΣ_(i=1)^(N−1)(I−S_(i,i+1)).
所有项都非负，基态唯一：为
全up态（相邻交换不变＋首位必须up）。
取单magnon归一化前试探态
  ψ_N=Σ_(i=1)^N(i−1)|i>,
其中|i>是只有第i位down的基向量。
ψ_N与全up真空正交，且
  <ψ_N,H_Nψ_N>=J(N−1),
  ||ψ_N||²=Σ_(i=1)^N(i−1)²
         =(N−1)N(2N−1)/6.
Rayleigh–Ritz给出
  0<gap(H_N)≤6J/[N(2N−1)] ~3J/N² ->0.

写作有隙product参考+局部扰动，
  H^0_N=Σ_i h_i  (gap=1),
  V_N=−Σ_(i=2)^N h_i
          +JΣ_(i=1)^(N−1)(I−S_(i,i+1)).
V_N的每个局部相互作用范数O(1)
且作用范围固定，与N无关，
但**不满足足够小的相对局部扰动条件**。

因此“每个块有隙，边界交互局部有界”
不蕴含全系统uniform gap，甚至在
真正唯一真空情况下也不蕴含。
这是完全可验证的 spin toy；不声称
为Yang–Mills物理反例。

## 7. 重要的RG及OS/时间生成元实际对应缺口

- 第59、63轮原B14和同Schwinger源码
  仅通过显式模型Gram/源/极限输入
  推出 CONTINUUM spectral gap。
- 第67轮 Yarotsky/J.Stat.Phys/CMP已发表
  稳定性定理确实能在其技术条件下
  从有隙独立块＋充分弱局部作用推出
  体积一致有隙。
- 真实KS块在强/中等coupling局部有隙
  并不表明已经获得一个严格的
  RG终端分解
     H^phys_Λ=Σ_B h^phys_B+Σ_X V_X
  且 \sup_BΣ_(X contains B) weight(X)||V_X||
  小于已发表稳定性定理允许的阈值。
- 实际Gauss界面约束、共用链接、非局部
  center/toron扇区可能使物理Hilbert不
  等于简单的局部块tensor product。
- 完整四维欧氏Wilson RG后的正时间
  转移未被证明与空间局部KS块Hamiltonian
  酉等价，特别是一般有效作用可能含
  非局部时间核。
- 裸微观g(a)→0，与终端块上g_eff
  是否属于可用相互作用弱区域是不同
  命题。原Bałaban U1 old/new-R控制不
  保证非微扰强耦合入口或所需H2。
- 不应把此处已解决的**isolated local block gap**
  误报成整个实际SU2终端IR的gap。

下一纸面主目标是找到一种真正保持
时间反射、Gauss约束和体积统一local norm
的非微扰RG终端Hamiltonian精确表示，
并证明其块间交互满足现有稳定性门槛；
或绕过有隙块强条件直接证明
Original15所用同一个真实T_*的
完整非真空Gram收缩。

## 8. 本轮验收

历史39/39 CONDITIONALLY PASS，原主定理未改。
本轮新增数学结果：
- SU2 Gauss单plaquette精确Jacobi/Sturm等价；
- 固定g局部gap、强g显式lower、弱g半线振子极限；
- 单plaquette all-positive-g统一dimensionless gap；
- 任意固定尺寸SU2 KS块compact参数uniform local gap；
- 四组严格整数Sturm+无限尾误差认证；
- unique-vacuum bounded local interactions的L^-2 gapless反例。
本轮新增Lean：0；I7 paper OPEN；4D质量隙OPEN。

相关已发表工作：Kogut--Susskind Hamiltonian的
真实公式可见 *Dynamics in hamiltonian lattice gauge theory:
approaching the continuum limit with partitionings of SU(2)*,
Eur.Phys.J.C (2025), DOI 10.1140/epjc/s10052-025-15120-x；
Yarotsky, CMP 261 (2006),799–819，
DOI 10.1007/s00220-005-1456-9，提供适当局部
弱扰动下的谱隙稳定性理论。
Clay数学研究所仍将 Yang–Mills & Mass Gap 标注Unsolved。
