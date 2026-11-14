# 第63轮｜真实 Wilson 源的罕见坏场剥离与 B14 源依赖误差

日期：2026-11-14
研究分支：ym-i7-sourcewise-rare-20261114
继承第62轮：ym-i7-uv-exponent-capacity-20261114
状态：原历史 39/39 CONDITIONAL；**物理 I7 OPEN**；无条件四维 Yang--Mills 质量隙 OPEN。

## A. 本轮最短证明链发生的实际变化

第62轮的两态反例严格说明：
  μ(B) -> 0
不能推出整个有限截断 transfer 的谱隙统一为正，
因为正交归一化坏模态可极端滞留。

但是第59轮已经核验的**仅连续体** B14 不需要
全体有限截断算子的谱上界；它只需要
对每个固定有限物理正时间 Wilson 源 F，
完整同一测度的 Gram 误差在同一联合极限中趋零。

因此，对固定有界源，坏场逃逸容量下界并非
**逻辑上必需**的独立输入；只要坏场对该固定源的
Gram 贡献趋于零即可。这绝不说明好场本身已收缩。

## B. 精确有限 Wilson/Gibbs 期望分解

取同一个真实 EUCLIDEAN SU(2) Wilson 概率测度 μ_k
（它在所需时刻满足 RP/反射兼容）和固定有限正时间
Wilson 多项式 F_k=∑_{j∈s} c_j [W_{j,k}−μ_k(W_{j,k})]。
在一致的反射 Θ 和物理时间平移 τ_t 下定义

 Q0(k;s,c)=Re E_{μ_k}[conj(ΘF_k) F_k],
 Qt(k;s,c)=Re E_{μ_k}[conj(ΘF_k) τ_t F_k].

任取可测的坏场事件 B_{k,s,c}，G=B^c，
都使用 SAME μ_k。只需在好场上直接验证
  Re E[1_G conj(ΘF_k) τ_t F_k]
    <= q Re E[1_G conj(ΘF_k) F_k],
其中 0<q<1 对所有固定源及所有调节参数一致。
注意：1_G 加权形式本身不一定 RP，这里只用普通
欧氏积分不等式，**没有**把条件期望视为OS投影。

若 |F_k|,|ΘF_k|,|τ_tF_k|<=M_F，则严格得到
  Qt(k;s,c)-q Q0(k;s,c)
    <= (1+q)M_F² μ_k(B_{k,s,c}).                 (63.1)

对物理单个 SU2 trace，|tr(U)|<=2。
中心化后 |W−μ(W)|<=4。固定有限多项式满足
  M_F <= 4∑_{j∈s}|c_j|
在所有裸截止一致（即使每个物理 loop 经过日益多
微观链路，其群 holonomy 始终在 SU2 中）。
因而
  Qt <= q Q0 + 16(1+q)(∑|c_j|)² μ_k(B_{k,s,c}). (63.2)

若对每个固定 s,c，μ_k(B_{k,s,c})->0，则当前
Wilson 有界源所需的 BAD-ERROR 已闭合为一个
源依赖、绝对且在极限中消失的量。
这**不是**好场严格收缩的证明，也**不是**证明
坏场局部化/概率界（见 §E）。

## C. 从 L∞ 改进为高矩的严格 Hölder 形式

如果源不是一致有界，而存在 p>1 的真实测度矩界

 sup_k [ ||ΘF_k||_{2p} + ||F_k||_{2p}
              + ||τ_tF_k||_{2p} ] <= 3M_p,

则 Cauchy--Schwarz/Hölder 给出
  |E[1_B conj(ΘF_k) τ_tF_k]|
    <= M_p² μ_k(B)^(1−1/p),
同样适用于 t=0。于是
  Qt <= qQ0+(1+q)M_p² μ_k(B)^(1−1/p).           (63.3)

当 p=2 只需一致 L4 矩界，bad-error 是 O(sqrt(μ(B)))。
更一般的充分条件是相关两根
|F_k|² 在真实 μ_k 下对小概率事件一致可积，
不一定需要固定 p>1。

源矩界真实来源不可跳过：
 YMOriginal/Original30_SourceJointUniformBound.lean
和 YMOriginal/Original30_WilsonProbabilityMoments.lean
的控制仍显式要求 Wilson 源系数预算
  actualWilsonPolynomialBudget(...) <= K
而物理重整化曲率源、局部场的 cutoff-uniform K 未证明。
不能把这些 Lean 模块直接当成(63.3)的 producer。

## D. 精确慢陷阱反例表明两种目标的真正区别

取第62轮可逆两态模型：
 pi(B)=epsilon, P(B,G)=epsilon²,
 P(G,B)=epsilon³/(1−epsilon),
非真空慢特征值 lambda_bad=1−epsilon²/(1−epsilon)。

再张量加入独立、非真空特征值 q_good=0.6 的
二态 good 链。取固定有界 centered probe
  F=F_good+[1_B−epsilon].
此时
  Q0(F)=1+epsilon(1−epsilon),
  Q1(F)=0.6+epsilon(1−epsilon)*lambda_bad,
  Rayleigh(F)=Q1/Q0 ->0.6
尽管
  ||T|vac^perp||>=lambda_bad ->1。

epsilon   full operator norm      fixed bounded probe ratio
0.2       0.950000000             0.648275862
0.1       0.988888889             0.632110092
0.02      0.999591837             0.607681444
0.01      0.999898990             0.603920190
0.001     0.999998999             0.600399200

精确残差
  Q1(F)-0.6 Q0(F)
    =epsilon(1−epsilon)(lambda_bad−0.6)
    <=0.4 epsilon ->0。

相反，令
  H_bad=(1_B−epsilon)/sqrt(epsilon(1−epsilon)),
则 ||H_bad||_2=1，其supnorm~epsilon^(-1/2)增长，
Rayleigh(H_bad)=lambda_bad->1。这样的
截止依赖归一化源不能被简单的有界源小概率论证忽略。
因此最终连续体物理 Hilbert/局部 test algebra 的
稠密性、非平凡性以及物理重整化词典不可省略。

本例是 EXACT FINITE MARKOV TOY，不是 4D SU2 物理结论。

## E. 可实际检查的粗大场概率—几何量纲门槛

假设一个固定物理四维源窗有 O(a^(-4)) 个
微观区域，每个区域的真实坏场概率满足
  μ_a(B_{a,x}) <= C exp(−c/g²(a)),
且对小a具有一环形式
  1/g²(a) ~ 2b0 log(1/a),
  b0(SU2)=11/(24π²)=0.0464388758.

未经任何独立性假设，union bound 给出
  μ_a(∪_x B_{a,x})
     <= C' a^[2b0 c−4+o(1)].

若有界 Wilson 源 supnorm O(1)，要以该具体
union-bound 方法保证坏事件概率消失，
需要严格的 **充分** 门槛
  2b0 c>4, c>48π²/11≈43.06736。

若 renormalized 源 supnorm≤C a^(−r)，
式(63.1)的绝对误差至多 O(a^[2b0 c−4−2r])，
需 c>(4+2r)/(2b0)。

IMPORTANT: 这只是将单元的大场指数压低估计、
微观区域个数及裸 supnorm 合成的粗方法门槛。
实际 Bałaban p0(g)、大场定义、源局部几何、
RG 归一化和c值未在本轮证明或核定；
不能把c=43或任何假设值宣称为杨–米尔斯阈值。

尤其**不能**把坏场事件定义为
“整个无穷空间某处有一个坏胞元”，因为其概率
通常会接近1。必须建立SOURCE-LOCAL bad事件，
并对窗外场影响作真实的RG/聚类估计。
局部化步骤本身可能触及未闭合的红外影响，
所以绝不把它视为自动成立。

## F. 另一个非微扰必需性检验：好场 Gaussian 仍可能无隙

假设终端作用仅为线性化的无质量 Maxwell/Gaussian
模态，在空间边长L的三维环面，横向自由模的
最低非零频率为 |p|min=2π/L，因而固定物理时间t=1
传递因子
  q_free(L)=exp(−2π/L)->1 (L->infinity)。

L=8: q=0.455938;
L=16: 0.675232;
L=32: 0.821725;
L=64: 0.906490;
L=128:0.952098;
L=256:0.975755。

即使所有“坏场”都被排除，单靠自由 Gaussian
近似和其局部二次凸性也不能构造空间体积一致的
红外严格收缩。SU2质量的产生必须从完整非微扰
终端相互作用中证明。此图是自由场严格对照，
并非SU2物理频谱的证明。

## G. 新主链的严格 Lean 验收

新源：
 YMOriginal/Original42_B14SourcewiseRare.lean
新定理：
 YMUIC.Original42.b14_continuum_gap_from_sourcewise_error

相比第59轮的同一个全局err(k)和统一cost(s,c)，
新定理假设
   err : Finset J -> (J->Complex) -> Cut -> Real,
   forall s c, Tendsto (err s c) jointFilter (nhds 0),
   forall s c, Eventually (Qt(k,s,c)
       <= exp(−t d)Q0(k,s,c)+err(s,c,k)).
此量词正好容许在固定物理源后选SOURCE-LOCAL
坏场事件。继承相同正谱演算、Gram同网收敛和
连续体稠密性，得到gap(A_cont)>=d>0。
与上一轮一样，真实模型hcut尚未建立。

**官方严格 CI Success**：
 https://github.com/penghongzhong/YM-closed/actions/runs/43563378310
 Lean 4.35.0-rc3 / pinned Mathlib
 516d31250e96c4e8e76888c3d8e2e43a9642b9ee.
 #print axioms=[propext,Classical.choice,Quot.sound].
无sorry/admit/新增公理。
原39/39条件性主定理不变，新 theorem 只作为
第63轮一条实质放宽量词的辅助承重证明计数。

## H. 唯一红点：好场上的真正物理 IR 收缩

需要在同一真实Wilson测度、同一固定物理时间、
同一OS/Schwinger重构下证明：

  ∃q in (0,1) fixed for ALL sources and regulators,
  ∀ fixed finite physical source F,
  ∃bad events B_(k,F),
  μ_k(B_(k,F))->0,
  and
  Re E_{μ_k}[1_(B^c) conj(ΘF) τ_t F]
     <= q Re E_{μ_k}[1_(B^c) conj(ΘF) F]
  eventually along SAME joint cutoff-volume net.

Together with physical source L∞ or L^(2p) bounds
and the previously proved OS Gram convergence, this
would feed the sourcewise B14 and yield a positive
continuum mass gap without requiring finite-k
bad-sector escape rates.

**No such true SU2 good-sector contraction is proved.**
It is comparable in difficulty to the original mass-gap
dynamics, although the bad-field error and worst-volume
capacity burden have been isolated.

The published original U1 old/new-R polymer statements
do NOT establish this good-sector IR contraction.
The Clay Mathematics Institute still records
Yang–Mills existence and the mass gap as UNSOLVED.

## I. Final closure tree
4D SU2 U–I–C
├── GREEN original 39/39 CONDITIONAL
├── GREEN Round55-62 strict prior Lean auxiliary results preserved
├── GREEN Round63 finite same-Wilson-probability rare-event splitting (paper)
├── GREEN Round63 sourcewise B14 strict Lean CI 43563378310
├── GREEN exact reversible bad-mode toy: full gap vs bounded probes
├── YELLOW true Wilson renormalized-source uniform integrability and source-local bad probability
├── YELLOW same-Schwinger/OS physical Hilbert matching and fixed physical-time Gram limits
├── RED true full terminal SU2 good-field IR contraction q<1
└── RED actual original I7 and unconditional Yang--Mills gap remain OPEN.

## J. Reproducible bundle
Current-turn generated bundle: I7_round63_rare_modes_bundle.zip.
It includes Python, CSV, 2 exact-toy figures and a Chinese README.
Do not describe these as actual four-dimensional SU2 lattice simulations.
