# 基準與數學輸出（2026-11-12，含十三個新模組與 `ctt` 核心）

環境：Linux x86_64 sandbox；`moon 0.1.20261104` / `moonc v0.10.20+65efd5b93`；native target；單調時鐘，5 次平均（另有註記者除外）；資料決定性（固定 LCG 種子）。

測試：`moon test --target wasm` **262/262**、`moon test --target native` **262/262**。`moon check` **0 錯誤、0 警告**。

健檢：`python3 scripts/health.py` → 死碼 **0**、重複函式體 **0**。

## 1. 基準

```text
MoonBit derived-mathematics benchmark
toolchain: moonc v0.10.20+65efd5b93, target native
rank 512x512 us: bitset 47028.649399999995, scalar 2517312.9658, speedup 53.527222191501
matmul 256 us: bitset 6631.883199999999, scalar 837333.37, speedup 126.25876312176307
bar construction BZ/2 degree 8 us: 11836.7726
surjection operad E(4) through degree 3 us: 503212.7284
Wick 16-point us: DP 26118.0216, brute 1360981.7267999998, speedup 52.108913440825084
Milnor number E8 us: 693.96
Heisenberg commutator check us: 34391.3002
ua-beta exhaustive Fin 6 (720 equivs) us: 14186.4806
comp in U x50 (Fin 6 lines) us: 7062.630999999999
cofibration entailment n=6 x200 us: 165241.71740000002
checksum 14742
```

## 2. 原有模組：同調與結構

```text
S^2: V=4 E=6 F=4 chi=2 beta=[1, 0, 1]
T^2: V=9 E=27 F=18 chi=0 beta=[1, 2, 1]
RP^2: V=6 E=15 F=10 chi=1 beta=[1, 1, 1]
Mobius: V=6 E=15 F=9 chi=0 beta=[1, 1, 0]
transport of AND along ua(not) = OR (table code): 14
univalence round trips verified for Fin 4: 24/24
BZ/2 betti: [1, 1, 1, 1, 1]
bar Z/2 through 7: [1, 1, 1, 1, 1, 1, 1, 1]
E(4) betti: [1, 0, 0, 0]
A-infinity exterior algebra OK: true
A-infinity line dga OK: true
Heisenberg character p(0..8): [1, 1, 2, 3, 5, 7, 11, 15, 22]
Milnor A2: 2
Milnor E8: 8
Tjurina E7: 7
Kronecker Ext^0, Ext^1: 1, 1
```

## 3. 十三個新模組與 `ctt` 核心

```text
--- rewriting: decidability and confluence ---
Knuth-Bendix completion of group theory us: 7068.661599999999
  steps=17 rules=10 succeeded=true pending=0
  word problem: a*i(a)=e true, i(i(a))=a true
  LPO terminating=true, locally confluent=true

--- demorgan: De Morgan cubical algebra ---
free De Morgan algebra on 2 generators us: 285351.0082
  |DM(0)|=2, |DM(1)|=6, |DM(2)|=168

--- deform: deformation functor and tower of modules ---
HH^2 of the dual numbers over F_5 us: 186.0736
  F_5: HH^0=1 HH^1=0 HH^2=0
  dual: HH^0=2 HH^1=1 HH^2=1
  F_5 x F_5: HH^0=2 HH^1=0 HH^2=0

--- fiber: derived fiber product ---
derived fiber (x^2) vs (x), 2 vars deg<=6, us: 64.6508
  (x) vs (y): Tor=[1, 0] classical=1 serre=1 transverse=true
  (x) vs (x): Tor=[7, 6] classical=7 serre=1 transverse=false
  (x^2) vs (x): Tor=[7, 5] classical=7 serre=2 transverse=false

--- gauge: connection, curvature, horizontal distribution ---
Bianchi d_A F = 0 on every cube of a 3x3x3 grid over S_3 us: 124.1316
  flat S_3 connection on 3x3: leaves=6 leaf size=9 integrable=true
  random S_3 connection on 3x3x3: flat=false bianchi=true

--- omega: weak omega-groupoids and the groupoid model ---
H^3(Z/3, Z/3) by exhaustive cocycle enumeration us: 187191.27033333332
  H^3(Z/2, Z/2): |Z^3|=2 |B^3|=1 |H^3|=2
  H^3(Z/3, Z/3): |Z^3|=27 |B^3|=9 |H^3|=3
  H^3(Z/2, Z/3): |Z^3|=1 |B^3|=1 |H^3|=1
  pi_1 rank: circle=1 wedge2=2 theta=2
  UIP: discrete 3-point set=true, Z/2 as a groupoid=false
  based path space contractible=true, J beta=true

--- cover: universal covering space and local fillability ---
universal cover of the figure eight, radius 3, us: 30.199599999999997
  circle: 9 points, tree=true local bijection=true
  figure eight: 53 points, tree=true local bijection=true
  local complementability audit of a constant cubical type: boxes=18 failures=0 Kan=true

--- adjoint: adjoint logic ---
adjoint proof search (dereliction !A |- A) us: 4.024050000000001
  exponential laws for !A = down-up A: dereliction=true dig=true contraction=true weakening=true
  shift adjunction holds=true

--- nbe: symbolic execution and normalisation by evaluation ---
symbolic execution of a 2-variable program us: 10.6879
  paths: NbE residual tree=4 after feasibility pruning=3
  soundness against concrete evaluation: 4 assignments, 0 mismatches; partition=true
  NbE beta-normal form: if 1 then if 0 then 1 else 2 else if 1 then 3 else 4

--- operad: little cubes ---
pi_0 of the discretised C_2(3) (504 placements) us: 2422.683
  pi_0 C_1(2)=2 C_1(3)=6 (k! orderings)
  pi_0 C_2(2)=1 C_2(3)=1 C_3(2)=1 (connected)
  swap possible: n=1 false, n=2 true, n=3 true

--- chordarc: chord-arc triangulated polyhedra ---
Floyd-Warshall on the subdivided octahedron (26 vertices) us: 1202.1592
  tetrahedron: V=4 F=4 chi=2 chord-arc=1/1 closed=true
  octahedron: V=6 F=8 chi=2 chord-arc=181/128 closed=true
  hairpin(2): V=14 F=12 chi=1 chord-arc=448/143 closed=false
  hairpin(6): V=30 F=28 chi=1 chord-arc=7/1 closed=false
  subdivision shortens the octahedron's opposite-vertex geodesic: 2896 -> 2508 (2*sqrt2 -> sqrt6, in units of 1/1024)

--- ctt: the type-directed Kan kernel ---
kernel ua-beta exhaustive Fin 6 (720 equivs, 4320 checks) us: 36958.58266666667
kernel transport in Fin 10^6 (per call) us: 8.283785
  comp in a space of 1000^1000 functions, applied at 7: #21
  ua endpoints are strict: Fin(1000000) -> Fin(1000000)
  ua-eta on ua images (readback equal): true
  J on refl reduces to the given element: #2
```

## 4. `ctt` 核心與枚舉式的對照

同一台機器、同一次執行：

| 項目 | 枚舉式 | 核心 `ctt` |
|---|---|---|
| uaβ 窮舉 Fin 6（720 等價） | 14.19 ms | 37.69 ms（4320 次檢查） |
| `Fin 10⁶` 上的傳輸 | 不可行（需列舉 10⁶ 個元素） | **8.54 µs／次** |
| `1000^1000` 個元素的函式空間中的合成 | 不可行 | `O(1)`，結果 `#21` |
| 餘纖維蘊涵，2 方向（n=6） | 279.5 µs／次（`3^6` 枚舉） | **0.57 µs／次（490×）** |
| 餘纖維蘊涵，200 文字、方向 5000+ | **跑不動**（`3^5200`） | **783 µs／次** |
| `Fin 1000` 傳輸，有向 `coe` | — | 7.07 µs／次 |
| `Fin 1000` 傳輸，雙向 `coe_between`（經插值線） | — | **4.02 µs／次** |
| `coe^{r→r}` 對角嚴格恆等 | — | **0.073 µs／次** |

最後兩列是第三輪的重點：舊判定不是「比較慢」，而是在核心真的需要它的地方
**完全無法執行**（方向從 100 起跳）。結構判定把方向數量的上界整個拿掉。

核心在小型別上仍較慢（閉包配置是常數因子開銷），換到的是漸近行為：
代價隨**型別語法樹**成長，而非隨**元素個數**成長。
枚舉版留下來只當測試 oracle——它另外能回答「填充唯一嗎」。

## 5. 每套件測試數

| 套件 | 測試 | 套件 | 測試 |
|---|---|---|---|
| core | 13 | rewriting | 8 |
| cubical | 22 | demorgan | 10 |
| **ctt** | **96** | deform | 10 |
| homotopy | 10 | fiber | 8 |
| algebra | 14 | gauge | 8 |
| derived | 8 | omega | 10 |
| cover | 9 | adjoint | 10 |
| nbe | 10 | operad | 8 |
| chordarc | 8 | **合計** | **262** |
