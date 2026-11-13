# moonmath — 編譯期導出數學（MoonBit）

[![CI](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml/badge.svg)](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

Repository: <https://github.com/vv0101v01/alge3>

以 MoonBit 由零實作的有限、可驗證高階數學引擎：

- **core**：GF(2) 位元向量與位並行線性代數（rank、Boolean 矩陣乘）、鏈複形、持久同調、有限體 `F_p`。
- **homotopy**：單純複形與三角剖分（S¹、S²、T²、RP²、Möbius）、內角填充（擬範疇）、么半群神經／棒複形、span/correspondence 合成。
- **algebra**：自由 Monad 與 substitution、Eilenberg–Moore fold、常數摺疊、A∞（Stasheff）、E∞（surjection operad 可縮性）、VOA（Heisenberg 模式、Wick DP、特徵標、rank variety）。
- **derived**：加權齊次奇點的 Milnor／Tjurina 數與 Hilbert 函數（ADE）、箭圖表示的 Ext⁰/Ext¹。
- **cubical**：把單價公理變成立方體演算法——區間的 De Morgan 代數、面格、Glue 類型、comp/hcomp/transp、$\mathsf{ua}$ 與 uaβ 計算（有限立方體模型，專文 `docs/cubical.md`）。
- **ctt**：**可計算單值性立方類型論核心**——Kan 頂蓋依類型結構遞迴**算出**（`Π` 得 lambda、`Σ` 得配對、`Path` 得維度抽象、`U` 得 `Glue`、HIT 得形式合成），而非窮舉搜尋；`fill` 由聯絡導出、`coe` 為空管壁合成、正則律為計算規則。等價帶著**纖維可縮性**資料，`equiv` 運算與修正方形使 `Glue` 合成對**非嚴格**等價成立；`uaβ` 對任意型別嚴格成立，`uaη` 對**任意路徑**有構造見證（像上為定義等式）。**無界**：餘纖維蘊涵結構判定（與方向數量無關）、轉換判定無深度上限、離散函式在中性元上完備。HIT 齊備（`S¹`、`Susp`、`∥A∥`），含 `isProp → isSet`。可在 `Fin 10⁶`、`1000^1000` 函式空間與 Cantor 空間 `Nat → Bool` 上執行（專文 `docs/ctt.md`）。
- **rewriting**：可判定性與合流性——合一、臨界對、LPO 終止性、Knuth–Bendix 完備化（群論字問題 17 步收斂）。
- **demorgan**：德摩根立方體代數——反鏈正規形、自由代數（1 生成元 6、2 生成元 168）、立方體恆等式窮舉。
- **deform**：形變函子與模塔——Artin 局部環、小擴張、Hochschild 上同調 HH⁰/HH¹/HH²、Gerstenhaber 障礙、剛性判定。
- **fiber**：衍生纖維積——Taylor 解消、Tor、Serre 交截重數、橫截性、分次 Euler 特徵。
- **gauge**：聯絡、曲率與水平分佈——有限結構群、Wilson 線、plaquette 曲率、Frobenius 可積性、Bianchi 恆等式、規範協變性。
- **omega**：弱 ω-群胚與高維群胚模型——球狀集、嚴格 ω-範疇（含 interchange）、自由群胚與 π₁、UIP/J 的群胚模型、弱 2-群與 H³ 分類。
- **cover**：泛覆疊空間與路徑類型局部可補性——路徑纖維化、樹性質、局部雙射、deck 群 ≅ π₁、Kan 填充的有限審計。
- **adjoint**：伴隨邏輯——模式預序、獨立性宣告、上下移位、`↓ ⊣ ↑` 伴隨、`!A = ↓↑A` 的餘單子律、切可容許、保守性；無收縮片段為**可判定**。
- **nbe**：符號執行與 NbE 整合——符號執行**就是**帶自由變元的 NbE 加讀出決策樹；路徑條件用德摩根代數，可行性與等價是兩個不同的判定。
- **operad**：小立方體算子——精確整數仿射合成、算子公理、Dunn 可加性；以有限 BFS 算出 π₀(C_n(k))：`n=1` 得 `k!`、`n≥2` 得 1。
- **chordarc**：弦弧三角多面體——整數測地線、精確有理弦弧常數、重心細分、定量局部可補性。
- **bench**：可執行基準；**docs/paper.md**、**docs/advanced.md**、**docs/ctt.md**：定理、定義、算式與複雜度分析。
- **scripts/health.py**：全倉庫健檢——死碼掃描、重複函式體偵測、套件行數（目前：死碼 0、重複 0、編譯警告 0）。

## 工具鏈

```text
moon 0.1.20261104 / moonc v0.10.20+65efd5b93 (2026-11-04)
```

安裝：`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash`，然後 `export PATH="$HOME/.moon/bin:$PATH"`。

## 快速開始

```bash
git clone https://github.com/vv0101v01/alge3.git
cd alge3
export PATH="$HOME/.moon/bin:$PATH"
moon test --target wasm        # 262/262
moon test --target native      # 262/262
moon run --target native bench # 數學摘要 + 基準
```

或者一鍵跑齊（會自動安裝工具鏈）：

```bash
./scripts/check.sh
```

## 基準（native，5 次平均）

| 項目 | 位並行／DP | 純量／樸素 | 加速 |
|---|---|---|---|
| GF(2) rank 512×512 | 23.8–24.3 ms | 1.03–1.10 s | **43–45×** |
| Boolean matmul 256³ | 3.1–4.0 ms | 315–393 ms | **98–102×** |
| Wick 16 點 | 12.5 ms | 517–592 ms | **41–47×** |
| BZ/2 至度 8 | 4.6 ms | — | — |
| E(4) 至度 3 | 194–244 ms | — | — |
| Milnor E₈ | 0.22–0.27 ms | — | — |
| uaβ 窮舉 Fin 6（720 等價） | 6.9 ms | — | — |
| $\mathcal U$ 中 comp ×50 | 2.8 ms | — | — |
| 面格蘊含 n=6 ×200 | 60–70 ms | — | — |
| Knuth–Bendix 群論完備化 | 3.8 ms | — | — |
| 自由德摩根代數（2 生成元，168 元素） | 174 ms | — | — |
| HH²（對偶數，F₅） | 95 µs | — | — |
| 衍生纖維積（2 變元，次數 ≤ 6） | 41 µs | — | — |
| Bianchi 恆等式（3×3×3，S₃） | 74 µs | — | — |
| H³(Z/3, Z/3) 窮舉 | 93 ms | — | — |
| 泛覆疊（8 字形，半徑 3） | 17 µs | — | — |
| 伴隨邏輯證明搜索（dereliction） | 2.0 µs | — | — |
| 符號執行（2 變元程式） | 4.6 µs | — | — |
| π₀(C₂(3))（504 個構形） | 1.3 ms | — | — |
| 測地線（細分八面體，26 頂點） | 592 µs | — | — |

## 數學結果（節選）

- `S²: V=4 E=6 F=4 χ=2 β=[1,0,1]`
- `T²: V=9 E=27 F=18 χ=0 β=[1,2,1]`
- `RP²: V=6 E=15 F=10 χ=1 β=[1,1,1]`（F₂ 係數；RP² 不可定向）
- `Möbius: V=6 E=15 F=9 χ=0 β=[1,1,0]`
- `BZ/2` 的 F₂ 同調：每個度數維度 1（週期性）
- `BZ/3`：`[1,0,0,0,0]`（3 在 F₂ 可逆）
- Surjection operad `E(4)`：`[1,0,0,0]`（可縮）
- A∞ 三例全部通過 `m₁²=0`、Leibniz、Stasheff m₃
- Heisenberg 特徵標係數：`1,1,2,3,5,7,11,15,22`
- ADE：A₁=1、A₂=2、A₄=4、D₄=4、E₆=6、E₇=7、E₈=8（μ=τ）
- Kronecker (1,1)：Ext⁰=1、Ext¹=1
- `transport (ua e) = e`（uaβ）：Fin 3、Fin 4 全部等價窮舉成立；`idtoeqv` 與 `ua` 兩邊來回程成立
- 沿 `ua(not)` 搬運布爾運算：AND → OR、OR → AND、XOR → XNOR（De Morgan 由 comp 計出）

### 十三個新模組（節選）

- **群論 Knuth–Bendix**：17 步、10 條規則、0 條剩餘等式；`a·i(a)=e` 是**導出**的右逆律。
- **自由德摩根代數**：0/1/2 生成元 → 2 / **6** / **168**；補律與 Kleene 不等式**實測失敗**。
- **剛性**：`F_5` 與 `F_5×F_5` 的 `HH¹=HH²=0`（剛性）；對偶數 `HH¹=HH²=1`（可形變）。
- **衍生纖維積**：`(x²)` vs `(x)` 的 `Tor=[7,5]`、**Serre 重數 2**；`(x,y,z)` 自交 `Tor=[1,3,3,1]`（Koszul）。
- **規範場**：平坦 ⟺ 可積（3×3 上 6 片葉 × 9 點）；**Bianchi `d_A F = 0`** 在 3×3×3 的每個立方體、`Z/5` 與 `S₃`、非平坦資料上全數成立。
- **弱 2-群**：五邊形公理 **就是** 群 3-上循環條件；`|H³(Z/2,Z/2)|=2`、`|H³(Z/3,Z/3)|=3`、`|H³(Z/2,Z/3)|=1`；非平凡類**不可嚴格化**。
- **群胚模型**：離散群胚滿足 UIP，非平凡群作為單物件群胚**違反 UIP**；基於路徑空間可縮（J 的健全性）。
- **泛覆疊**：圓的泛覆疊是線（9 點，樹、局部雙射）；8 字形是 4-正則樹（53 點）。
- **局部可補性**：常數立方體型別 18 個盒子、0 個失敗（Kan）；不相容盒子被偵測並拒絕。
- **伴隨邏輯**：`↓ ⊣ ↑`、`!A = ↓↑A` 的四條餘單子律全部導出；切可容許；線性片段保守。
- **NbE ↔ 符號執行**：與獨立代換式正規化器**逐字一致**；`x ∧ ~x` 在德摩根代數中**非零**但**不可行**——等價與可行性是兩個判定。
- **小立方體算子**：`π₀(C₁(3)) = 6 = 3!`、`π₀(C₂(3)) = 1`——`E₁` 不交換、`E₂` 交換，由可達性判定。
- **弦弧多面體**：正四面體常數 **1**、正八面體 **181/128 ≈ √2**、馬蹄形帶隨臂長線性成長（非一致弦弧）；重心細分把八面體對頂點測地線從 `2√2` 改善到 **`√6`**（真正的曲面測地線）。

## 文件

- 完整論文：`docs/paper.md`（HTML 版 `docs/paper.html`：單檔、公式內嵌成 SVG、無任何外部請求，離線可讀）。
- **十三個新模組專文**：`docs/advanced.md`（定義、定理、演算法、複雜度、實作陷阱、模組之間的接縫）。
- 基準原始輸出與說明：`RESULTS.md`。
- 方法論、定理、複雜度分析：論文 §1–§7；實作驗證 §8；限制 §9；立方體單價 §10。
- 立方體單價專文：`docs/cubical.md` / `docs/cubical.html`（定義、Glue/comp/ua 公式、有限單價定理及證明、複雜度）。

## 專案結構

```text
core/       GF(2) 位元向量、位並行線性代數、鏈複形、持久同調、F_p
homotopy/   單形複形、內角填充、神經／棒複形、correspondence
algebra/    自由 Monad、A∞、E∞（surjection operad）、VOA
derived/    Milnor／Tjurina、Hilbert 函數、箭圖 Ext
cubical/    區間/面格、CubeTy、Glue、comp、ua（立方體單價）
rewriting/  合一、臨界對、LPO、Knuth-Bendix 完備化
demorgan/   自由德摩根代數、反鏈正規形、立方體映射
deform/     Artin 環、Hochschild 上同調、形變函子、模塔
fiber/      Taylor 解消、Tor、衍生纖維積、Serre 重數
gauge/      有限群聯絡、曲率、水平分佈、和樂、Bianchi
omega/      球狀集、嚴格 ω-範疇、自由群胚、群胚模型、弱 2-群與 H³
cover/      泛覆疊、deck 群、圖覆疊、路徑類型局部可補性
adjoint/    模式理論、移位、伴隨、無切證明搜索
nbe/        NbE、βη 判定、代換式對照、符號執行與路徑條件
operad/     小立方體、算子公理、Dunn 可加性、π₀ 構形空間
chordarc/   整數測地線、弦弧常數、重心細分、流形檢查
ctt/        Kan 頂蓋演算法、comp/fill/coe、Glue+equiv、ua/uaβ/uaη、funext/J、
            h-層級+Hedberg、HIT（S¹/Susp/截斷/Coeq）、無界結構轉換、
            雙向 Kan 運算（transp/coe_between/comp_between/fill_between）、
            內部對稱（反轉對合、Kan 結構等變）
bench/      可執行基準（moonbitlang/core/bench）
docs/       paper.md / paper.html、cubical.md / cubical.html、advanced.md、ctt.md
scripts/    check.sh、health.py（死碼／重複／行數掃描）
```

執行 `moon test` 時每個 package 的 `*_wbtest.mbt` 即為對應定理的可執行版本（**262 個測試**，wasm 與 native 雙目標全綠；`moon check` 0 錯誤 0 警告）。

## 2026 MoonBit 語法注意

- `trait`/`impl` 方法要 `fn`；泛型寫 `fn[T] f`。
- `Int` = `Int32`；`UInt64` 用 `UL`。
- `moon.pkg` DSL；`using @pkg { type T, value }`；`using` 塊不接受 `fn`。
- 範圍 `for i in (a + 1)..<n` 要括號。
- 熱路徑已標 `#inline`；測試以 `moon test --target wasm` 執行。
- `#derive(Debug, Eq)` 寫在型別**上方**；跨套件建構 enum 需 `pub(all) enum`。
- 每個套件只能有**一個** `using` 塊（重複會報 4051）；集中在 `imports.mbt`。
- `inspect!` 已移除；斷言用 `assert_eq` / `assert_true`（或 `moonbitlang/core/test` 的 `@test.assert_eq`）。
- 記錄欄位當函式呼叫要括號：`(clo.f)(x)`；本倉庫改用 `Clo::at` 等存取方法。
- 含閉包的型別無法 `#derive(Debug, Eq)`；`ctt` 手寫 `Debug`（讀回渲染）與 `Eq`（無界結構轉換，兩邊共享探測變元與名字供應）。
- `guard`、`opaque`、`var` 是保留字，不能當欄位或變數名。
- 衍生 trait 的方法提升要明確寫 `pub extend T with Eq::{equal, not_equal}`（見各套件的 `extends.mbt`）。
- `Map` 用 `Map([])`；`Array::pop()` 回傳 `Option`；`Array::remove(i)` 的回傳值要 `ignore(...)`。
- 整數 LCG 要注意 `Int32` 溢位：`(s * 1103 + 12345) % 32768` 安全，`(s * 1103515245 + …) % 2147483647` 會溢位成負數。
