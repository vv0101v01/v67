# 可計算單值性立方類型論：Kan 頂蓋演算法與核心實作

本文件對應新套件 **`ctt/`**（1921 行，28 條執行測試），以及為它而做的全倉庫健檢。

一句話總結：**`cubical/` 是有限模型上的判定程序，`ctt/` 是類型論核心**。
前者的 `comp` 在有限預層的元素中**窮舉搜尋**填充；後者的 `comp` 依**類型結構遞迴**
把頂蓋**算出來**。兩者在倉庫中並存，互為對照：一個是可判定的語意模型，
一個是可執行的語法核心。

* 測試：`moon test --target wasm` **188/188**、`--target native` **188/188**。
* 編譯：`moon check` **0 錯誤、0 警告**。
* 健檢：`python3 scripts/health.py` → **死碼 0、重複函式體 0**。

---

## 0. 為什麼原來的 `comp` 不夠

`cubical/comp.mbt` 的原始實作，核心是這樣一段：

```text
for cand in 0 ..< x.card[gen]:            ← 走訪通用纖維的每一個元素
    if 每個面 φ_k 上 res(cand) = vals[k]:  ← 檢查是否與已知管壁相符
        收集 cand
return CompResult { lid, filler, fillers, unique_lid }
```

這是一個**判定程序**：它回答「這個開盒有沒有填充？有幾個？」。
對有限模型這是完全正確而且有用的（`cover/local.mbt` 的 Kan _audit_ 就靠它），
但它不是立方類型論的 Kan 運算，理由有三：

1. **複雜度錯**。代價是 `O(|A_generic|)`，而 `|A_generic|` 對 `Π`、`Σ`、`Path`
   是指數成長。`Fin 1000 → Fin 1000` 有 `1000^1000` 個元素，無法列舉。
2. **沒有計算內容**。它不會告訴你「`Π` 型的合成就是一個 lambda」——
   而那正是單值性得以計算的原因。
3. **無法給出 `uaβ`**。單值性的計算內容是「沿 `ua(e)` 傳輸 = 施加 `e`」，
   這需要 `Glue` 的合成規則，而搜尋法看不出 `Glue` 的結構。

`ctt/` 補上的正是這三點。

---

## 1. 分層

```
cubical/interval.mbt   區間 I 與餘纖維格 F（De Morgan 代數、代入、蘊含）
        ↓
ctt/value.mbt          值 Val、閉包 Clo/DClo、型族 Fam、管壁 Tube
ctt/kan.mbt            comp / fill / coe —— Kan 演算法本體
ctt/univalence.mbt     Equiv、ua、idtoeqv、路徑代數、funext、J、h-層級
ctt/quote.mbt          讀回（quote）：以 NbE 正規形做轉換判定
```

### 1.1 區間與餘纖維（共用，本輪擴充）

`Dim` 是自由 De Morgan 代數：`0, 1, i, ~r, r∧s, r∨s`。
`Cof` 是餘纖維格：`⊥, ⊤, (r=0), (r=1), φ∧ψ, φ∨ψ`。

本輪新增的通用代入（原本只有端點特例）：

| 函式 | 意義 |
| --- | --- |
| `dim_subst(t, i, r)` | `t[i := r]`，對 `∧/∨/~` 遞迴並常數折疊 |
| `dim_not / dim_and / dim_or` | 帶常數折疊的 De Morgan 運算 |
| `cof_subst(φ, i, r)` | `φ[i := r]` |
| `cof_and / cof_or` | 餘纖維的交與併 |
| `Dim::mentions / Cof::mentions` | 語法出現檢查，**正則律的判定依據** |
| `cof_leq(φ, ψ)` | 在面格上判定蘊含，**結構性、與方向數量無關** |
| `cof_faces(φ)` | 餘纖維的正規形：面的析取，每面是排序好的文字合取 |
| `cof_same / cof_is_true / cof_is_false` | 等價、恆真、恆假 |

#### 結構蘊涵（`cubical/faces.mbt`）

面格是面上的**自由分配格**，模 `(i=0) ∧ (i=1) = ⊥`。它**不是**布爾代數：
`(i=0) ∨ (i=1)` 是區間的邊界，嚴格低於 `⊤`。兩件事給出判定程序：

1. **面是 join-prime。** 一致的合取 `F` 滿足 `F ≤ ψ₁∨ψ₂`  iff
   `F ≤ ψ₁` 或 `F ≤ ψ₂`。語意上 `F` 有一般點（自己的方向釘死、其餘自由），
   而 Kleene 析取只有在一邊已是 `1` 時才回 `1`。
2. **每個餘纖維都是面的析取。** 把 `∧` 對 `∨` 分配即得析取正規形，
   丟掉矛盾的析取項。

於是 `φ ≤ ψ` iff `φ` 的每個面都在自己的一般點上 forcing `ψ`，
而 forcing 是一次 `O(|ψ|)` 的 Kleene 求值，對著**稀疏**賦值。
沒出現的方向完全不花錢。

維度項的展開是精確的：`(a∧b=1) ≡ (a=1)∧(b=1)`、
`(a∧b=0) ≡ (a=0)∨(b=0)`、`(~a=e) ≡ (a=1-e)`，其餘對偶。

正規形沿用 `interval.mbt` 既有的那份（`2i` 表 `(i=1)`、`2i+1` 表 `(i=0)`，
排序、去重、吸收），只多一條面格關係：同時含 `2i` 與 `2i+1` 的合取是 `⊥`
（維度項 `i ∧ ~i` 則只是自由，不是 `⊥`）。
`∧` 鏈的常見形狀走線性合併快路徑，否则每一環都跑二次正規化會變三次。

`cof_entails(φ, ψ, n)`（枚舉 `3^n`）保留為**測試 oracle**：
`faces_wbtest.mbt` 在 2 方向的 78 條公式、6084 個有序對上逐一比對，
再在 3 方向含維度項的宇宙上比對一次。

端點版本 `dim_subst_endpoint` / `cof_subst_endpoint` 已刪除——
它們是通用版本的特例，留著只是重複。

### 1.2 值與閉包：為什麼不需要值的代入

```moonbit
pub(all) enum Val {
  VU | VFin(Int32)
  VPi(Val, Clo) | VSig(Val, Clo)
  VPath(DClo, Val, Val)
  VGlue(Val, Array[GlueBr])
  VLit(Int32) | VLam(Clo) | VPair(Val, Val) | VPLam(DClo)
  VGlued(Array[GlueTm], Val)
  VNe(Int32)
}
```

`Clo` 是項閉包 `(Val) -> Val`，`DClo` 是**維度閉包** `(Dim) -> Val`，
兩者都是宿主（MoonBit）閉包。於是一個「沿某維度變化的型族」就是一個
`Dim -> Val` 的函式，而經典表述中每一處寫 `A[i := r]` 的地方，
這裡只是**再施加一次型族**。

> **設計後果**：核心中完全沒有「值的代入」這個操作。
> 唯一的語法代入發生在維度與餘纖維上，那是 `cubical/interval.mbt` 的事。
> 這消掉了立方類型論實作中最容易出錯的一整塊（綁定器捕獲、 freshness）。

---

## 2. Kan 演算法：計算開盒的頂蓋

### 2.1 問題

```text
        φ ↦ u(i)          管壁：在餘纖維 φ 上給定的一條線
      ┌───────────┐
      │           │
  i=1 ├ ─ ─  ─ ─ ┤  ←  頂蓋 (lid)：要求算出來的東西
      │           │
  i=0 └───────────┘
           a₀             底蓋：在 φ 上與 u(0) 相符
```

型別：`comp : (Fam, Int, Tube, Val) -> Val`，其中 `Fam` 是 `i ↦ A(i)`。
要求：`comp A [φ ↦ u] a₀ : A(1)`，且在 `φ(1)` 上等於 `u(1)`。

### 2.2 演算法（依類型結構遞迴，CCHM）

```text
comp A i [φ ↦ u] a₀ :=
  若 φ 中有分支為 ⊤        → u(1)                      （管壁已封閉，頂蓋被強制）
  若 A 與 u 都不依賴 i      → a₀                        （正則律／正規律）
  否則依 A(i) 的外層構造：

  Fin n   → a₀                                          離散型合成唯一
  U       → Glue [φ(1) ↦ (E(1), coe^{1→0} E)] a₀        宇宙中的合成即膠合
  Π(x:A).B→ λ(x:A(1)). comp B(x̃(i)) [φ ↦ u(i)(x̃(i))]
                              (a₀ (x̃(0)))               其中 x̃(i) = coe^{1→i} A x
  Σ(x:A).B→ (a₁, b₁)                                    a₁ = comp A [φ ↦ fst u] (fst a₀)
                                                        ã  = fill A [φ ↦ fst u] (fst a₀)
                                                        b₁ = comp B(ã(i)) [φ ↦ snd u] (snd a₀)
  Path (j.B) a b → <j> comp B(j) [φ ↦ u@j, j=0 ↦ a, j=1 ↦ b] (a₀@j)
  Glue    → 見 §3
```

每一條都是**等式**，不是搜尋。實作對應 `ctt/kan.mbt` 的
`comp_univ / comp_pi / comp_sig / comp_path / comp_glue`。

三個值得指出的細節：

* **`Π` 的反變性**：參數要沿定義域**往回**拖（`coe^{1→i}`），
  才能在餘定義域中往前合成。這個反變性就是整條規則的內容。
* **`Σ` 用填充而非頂蓋**：第二分量要在第一分量的**填充線** `ã(i)` 上合成，
  不是在 `a₁` 上。否則配對會落在錯誤的纖維。
* **`Path` 把端點加入管壁**：路徑型只要其體是 Kan，它自己就是 Kan——
  理由就在這條規則。

### 2.3 填充：只用合成與聯絡

```text
fill A i [φ ↦ u] a₀ (r) :=
  comp^{k} A(r∧k) [ φ[i := r∧k] ↦ u(r∧k),  r=0 ↦ a₀ ] a₀
```

`k` 是新鮮維度。這是唯一用到區間**聯絡** `∧` 的地方，也正是它把合成變成填充：

* `r = 0`：新增的分支 `r=0` 變成 `⊤`，管壁封閉，故結果**嚴格**等於 `a₀`。
* `r = 1`：聯絡退化為恆等，結果**嚴格**等於 `comp` 的頂蓋。

所以填充線的兩條邊界律是**構造上成立**的，不需要另外證明。
測試 `kan: filler boundaries hold by construction` 直接斷言這兩條。

### 2.4 傳輸

```text
coe^{0→1} (i.A) a := comp A i [] a          （空管壁的合成）
coe^{1→0} (i.A) a := coe^{0→1} (i.A(~i)) a  （反向族）
```

### 2.5 正則律是計算規則，不是事後定理

```moonbit
if fam.is_constant(i) && tube.is_constant(i) { return cap }
```

`Fam::is_constant` 用 `mentions` 做語法出現檢查。這一行的後果很大：

* `coe` 在常值族上是**恆等**，直接回傳原值，不重建。
* `comp` 在常值盒（型與管壁都不依賴方向）上回傳底蓋。
  這使得 **`uaβ` 對任意型別都嚴格成立**，而不只是離散型別。

> **本輪抓到的一個真實錯誤**：`is_constant` 最初在**新鮮變元** `probe` 上探測，
> 然後檢查結果是否提到 `i`。但在新鮮變元上施加，恰好把要偵測的方向依賴**代換掉了**。
> 正確做法是在**方向本身** `DVar(i)` 上探測。
> 症狀是「宇宙中的合成」被誤判為常值而直接回傳底蓋。

### 2.6 複雜度

| | `cubical.comp`（有限模型） | `ctt.comp`（核心） |
| --- | --- | --- |
| 依據 | 通用纖維的元素個數 | 類型語法樹的大小 |
| 代價 | `O(|A_generic| · |tube|)` | `O(|type| · |tube|)` 次遞迴 |
| `Fin 10^6` | 10^6 次檢查 | `O(1)` |
| `Fin 1000 → Fin 1000` | `1000^1000`，不可行 | `O(1)` 每次施加 |
| 回答 | 「有沒有填充？唯一嗎？」 | 「頂蓋是什麼？」 |

---

## 3. `Glue` 的合成：最難的一條，也是單值性的來源

設 `B(i) = Glue [ψ ↦ (T, e)] A`，其中 `e : T ≃ A`。
要求 `comp^i B [φ ↦ b] b₀`。演算法對每個分支分兩種情形：

### 情形 A：`ψ(0) = ⊤`（近端成立）

此時在 `ψ` 上 `B` **就是** `T`，所以底蓋 `b₀` 本身就是一個 `T`-元素：

```text
t₁ = comp^i T [φ∧ψ ↦ b] b₀
t̃  = fill^i T [φ∧ψ ↦ b] b₀
分支輸出 (ψ(1) ↦ t₁)
並把 ψ ↦ e(t̃) 加入底型的管壁
```

遠端的相容性 `e(1)(t₁) = a₁` 由管壁**強制**，不需要動用等價的任何性質。

### 情形 B：`ψ(0) = ⊥` 但 `ψ(1) = ⊤`（只在遠端成立）

底蓋**沒有**給出 `T`-元素。CCHM 在這裡**反轉遠端的等價**：

```text
t₁ = e(1)⁻¹ a₁
```

這需要 `a₁` 先算出來，所以實作把這個分支記在 `deferred` 裡，
等底型合成完再回填。**不加入管壁分支**：在這一面上相容性就是
`e(1)(e(1)⁻¹ a₁) = a₁`，即等價的嚴格截口律。

```text
a₁ = comp^i A [φ ↦ unglue b, (情形 A 的分支) ↦ e(t̃)] (unglue_{i=0} b₀)
b₁ = glue [ψ(1) ↦ t₁] a₁
```

### 3.1 三個容易寫錯的地方（本輪都踩過）

1. **`unglue` 必須在 `i=0` 這一階段做**。若某分支在 `i=0` 為 `⊤`，
   則該階段的型別**就是** `T`，底蓋是裸的 `T`-元素，它的底分量是 `e(0)(b₀)`。
   忘記這件事，`uaβ` 會回傳 `a` 而不是 `e(a)`。實作：`unglue_cap`。
2. **分支的餘纖維要在智能構造子折疊之前讀取**。
   `mk_glue_ty` 在某分支為 `⊤` 時直接回傳該分支的型別（這是 `Glue` 的面規則），
   於是「在端點階段讀取分支餘纖維」會讀到 `⊥`——分支資訊整個消失。
   實作：`raw(r)` 讀一般階段的分支，再用 `cof_subst` 自行特殊化。
3. **`Glue` 分支必須存整個等價，不能只存正向映射**。情形 B 需要 `e⁻¹`。
   只存 `Clo` 的實作根本寫不出這條規則。

### 3.2 智能構造子＝嚴格的面規則

```moonbit
mk_glue_ty(branches, base)  // 有 ⊤ 分支 → 直接回傳該型別
mk_glue(brs, base)          // 有 ⊤ 分支 → 直接回傳該項
```

這兩行就是 `Glue [⊤ ↦ (T,e)] A = T` 與 `glue [⊤ ↦ t] a = t`。
它們使得 `ua` 的端點**在鼻子上**成立（見 §4），不需要任何路徑代數。

### 3.3 等價資料：纖維可縮性（本輪補齊）

`Equiv` 現在帶著真正的 CCHM 資料：

```moonbit
pub(all) struct Equiv {
  src, tgt, fwd, bwd : Val
  alpha : Clo            // Π x. Path (bwd (fwd x)) x
  beta  : Clo            // Π y. Path (fwd (bwd y)) y
  contr : Contr          // Π y x q. Path (centre y) (x, q)  in fib fwd y
  strict : LazyBool      // 兩個來回都是定義恆等？（快路徑旗標）
}
```

`contr` 是**纖維可縮性**，不是「嚴格同構」的替代品。核心運算

```text
equiv e [ψ ↦ (t, p)] a = comp^k (fib e a) [ψ ↦ contr(a, t, p)(k)] (bwd a, β a)
```

在纖維型別中合成：盒子合法，因為 `contr(0)` 是中心、`contr(1) = (t, p)`。
這正是只給前向映射的實作**表達不出來**的那一步——在 `δ = ∀i.φ` 不成立的
`φ(1)` 上，它用的是 `g⁻¹`。

`comp_glue` 接著把底沿 `α(~j)` 拖回去（修正方形），使 `glue` 對
**非嚴格**等價仍然合法。嚴格同構時 `α ≡ refl`，修正步被 `strict` 旗標跳過。

**旗標而非讀回。** 是否在核心裡用 `quote` 比較兩個值來判斷嚴格性，
是會重入的：`quote` 探測閉包 → 閉包跑 `comp` → `comp` 又要判斷嚴格性。
實測會指數爆炸。`strict` 因此是每條分支**一次**、惰性、記憶化的判斷。

## 4. 單值性

### 4.1 `ua`

```text
ua(e) := <i> Glue [(i=0) ↦ (A, e), (i=1) ↦ (B, id_B)] B
```

端點**嚴格**：`i=0` 時第一分支為 `⊤`，智能構造子回傳 `A`；
`i=1` 時第二分支為 `⊤`，回傳 `B`。

### 4.2 `idtoeqv` 與傳輸

```text
idtoeqv(p) := (coe^{0→1} p, coe^{1→0} p)
transport p a := coe^{0→1} p a
```

### 4.3 `uaβ`：定義等式

> **定理（uaβ）** `transport (ua e) a ≡ e a`。

因為正則律是計算規則（§2.5），這對**任意型別**都是定義等式，
不只是離散型別。測試以讀回逐字比較，窮舉 `Fin 6` 的全部 **720** 個置換、
**4320** 個元素檢查。

### 4.4 `uaη`：對任意路徑成立

在 `ua` 嘅像上係**定義等式**。對**任意** `p : Path U A B`，
`ua_eta_general(p)` 係一個構造出嚟嘅見證，兩端都係定義等式：

```text
uaη(p) : Path (Path U A B) (ua (idtoeqv p)) p
```

構造見 §15。

### 4.5 宇宙中的合成

```text
comp^i U [φ ↦ E] A₀ = Glue [φ(1) ↦ (E(1), coe^{1→0} E)] A₀
```

注意方向：分支需要的是 `E(1) ≃ A₀`，所以**正向**映射是 `E` 的**反向**強制。
本輪抓到的第二個真實錯誤就在這裡：`fwd`/`bwd` 寫反了。
對合（involution）看不出來，對 3-循環立刻出錯——
所以複合傳輸的測試刻意用位移而不是對換。

### 4.6 等價代數

`equiv_id / equiv_comp / equiv_inv`，以及以讀回驗證三角恆等式的 `Equiv::check`。
測試涵蓋 `Fin 5` 全部 120 個置換，並驗證 `ua` 尊重複合與取逆。

---

## 5. 路徑代數、funext、J

全部由聯絡與合成定義，因此都會計算。

| 建構 | 定義 |
| --- | --- |
| `refl a` | `<i> a` |
| `path_sym p` | `<i> p(~i)` |
| `path_concat A p q` | `<i> comp^k A [(i=0) ↦ p(0), (i=1) ↦ q(k)] (p(i))` |
| `funext h` | `<i> λx. h(x)(i)` |
| `singleton_contract p` | `<j> (p(j), <i> p(i∧j))` |
| `pathJ P d p` | `transport (j. P (ηj).1 (ηj).2) d` |

**J 的計算規則是化簡**：當 `p = refl a` 時單元素線為常值，正則律觸發，
結果**嚴格**是 `d`。測試 `pathJ: the computation rule is a reduction` 斷言這一點。

`singleton_contract` 的兩端由聯絡強制：`j=0` 時 `i∧0 = 0` 把路徑壓成 `refl`，
`j=1` 時 `i∧1 = i` 是恆等。

---

## 6. h-層級

`is_contr / is_prop / is_set` 作為型別碼：

```text
isContr A = Σ(x:A). Π(y:A). Path A x y
isProp  A = Π(x y:A). Path A x y
isSet   A = Π(x y:A). isProp (Path A x y)
```

`contr_to_prop` 由 §5 的路徑代數構造 `λx y. (h x)⁻¹ · (h y)`，
`fin1_contr` 給出 `Fin 1` 的可縮性。這兩者都有測試。

---

## 7. 轉換判定：無界結構轉換

舊版把兩個值**印到深度 14** 再比字串。那是雙重近似：既截斷，
又會把截斷後同形的東西視為相等。本輪換成 `ctt/conv.mbt` 的結構_walk_：

* 依構造子逐一比對，**沒有深度參數**；
* 閉包兩邊探測**同一個**新變元，α-等價由構造保證，不靠命名慣例；
* 兩邊探測前把 `fresh_dims` 重設到**同一個基準**。閉包內部會自己分配方向
  （`comp` 每一步都會），若沿用上一個探測留下的計數，兩邊的內部名字會漂移，
  α-等價的值就被判成不等；
* η 律：`λ` 對非 `λ` 時兩邊同時作用再比；
* 等價只比 `src/tgt/fwd/bwd`——`alpha/beta/contr` 住在命題裡，
  比它們只是白跑一個 `J`。

**終止性。** 值域是全序型論的像：β-強正規化，正規形的構造子有限，
每次探測都揭露有限正規形的更多部分。`Val` 裡沒有不動點。
（构造子若捕捉**可變 cell** 會做出循環值——這是程式錯誤，
`unbounded_wbtest.mbt` 的塔因此逐層快照。）

`quote` 只剩渲染用途，深度只影響印出來的字串。

## 8. 驗證清單

`ctt` **96 條**，`cubical` **22 條**，全庫 **262 條**，wasm 與 native 雙靶全綠。

| 檔案 | 條數 | 內容 |
| --- | --- | --- |
| `ctt/kan_wbtest.mbt` | 8 | Kan 律：離散唯一合成、全管強制、Π/Σ/Path 分節、填充邊界 |
| `ctt/univalence_wbtest.mbt` | 14 | `ua` 端點嚴格、`uaβ` 窮舉 `Fin 6` 720 個置換（4320 次檢查）、反向傳輸、`uaη`、`Fin 5` 120 個嚴格同構、共軛傳輸、sym/concat/funext、單點可縮、`pathJ`、h-層級碼 |
| `ctt/scale_wbtest.mbt` | 6 | `Fin 10^6` 上的 `ua`、`1000^1000` Π 中的合成、複合路徑傳輸（9-循環）、`equiv_comp`/`equiv_inv` |
| `ctt/general_wbtest.mbt` | 11 | 纖維收縮、`equiv` 擴張偏元素、**非嚴格**等價的 `ua` 傳輸、Cantor 空間 `Nat → Bool` 上的單值性、中性元上的 case split、`contr_path_contr` 四面、`isProp → isSet`、`comp_path` 端點回歸 |
| `ctt/unbounded_wbtest.mbt` | 8 | 深度 14 之外才不同的值被分開、20 層綁定下的函式轉換、η、`fin_fun` 中性完備、`Nat` 遞歸與停住、`with_contr`、面正規形 |
| `ctt/hit_wbtest.mbt` | 12 | `S¹` 構造子與 `loop` 端點、路構造子上的 β、形式合成、消除器保持合成、`∥A∥` 是命題、截斷遞歸、`∥S¹∥` 可縮、`Susp`、`loop ≠ refl` |
| `ctt/ops_wbtest.mbt` | 11 | 插值線端點、雙向還原有向運算、對角正則嚴格、內部階段合成、來回、`transp` 邊條件、填充、`transp_path`、異質／同質一致 |
| `ctt/symmetry_wbtest.mbt` | 10 | 反轉對合、De Morgan、餘纖維自同構、**兩條推導等變**、家族／管壁反轉對合、路徑對合、等價群胚、`ua_sym`、反向填充、`ua·sym(ua)` 還原 |
| `ctt/ua_eta_wbtest.mbt` | 8 | `uaη` 基礎方形、`refl`（像之外）、複合線、反向線、24 置換、路徑代數、單值性係等價、無限型別 |
| `ctt/computational_wbtest.mbt` | 8 | 全鏈 `uaβ`（24 置換 × 4 點 × 5 運算）、`idtoeqv∘ua`、`ua∘idtoeqv`、非嚴格等價、Cantor 空間雙向、三段複合函子性、`transp_path` |
| `cubical/faces_wbtest.mbt` | 6 | 與 oracle 在 6084 對上窮舉一致、3 方向含維度項、格非布爾、矛盾即底、De Morgan 展開、方向 10000 與 200 文字合取 |

## 9. 缺口清單：全部補齊

第二版呢度列咗六項「誠實的剩餘邊界」，第三版補咗五項、留低 `uaη`。
**六項全部補齊，清單空咗。**

| 舊邊界 | 現況 |
|---|---|
| 一般等價的 `Glue` 合成（只支援嚴格同構） | **補齊**：`Contr` 資料、`equiv` 運算、修正方形（§3.3） |
| 一般路徑上的 `uaη` | **補齊**：`ctt/ua_eta.mbt`，路徑歸納 + 同資料 `Glue` 方形，兩端定義等式（§15） |
| `isProp → isSet`（Hedberg）未構造 | **補齊**：`ctt/hlevel.mbt`，二維盒子 |
| HIT 未實作 | **補齊**：`S¹`、`Susp`、`∥A∥`、`Coeq`，含形式合成（§13、§14.7） |
| 離散函式 `fin_fun` 在中性元上停住 | **補齊**：入核心，用 `vsplit`；舊版對非字面值傳回引數本身，令綁定子下嘅定理全部係空嘅 |
| 讀回深度有界（14） | **補齊**：無界結構轉換（§7） |

### 9.1 順手抓到的兩個核心錯誤

補齊的過程抓到兩個**既有**的錯誤，都不是新程式引入的：

1. **餘纖維蘊涵是指數的。** `cof_entails(phi, psi, n)` 枚舉 `3^n` 個子立方。
   核心每合成一步就分配一個新方向（從 100 起跳），所以這道牆
   在數學失效之前很久就先壓死實作。這正是「全部有限、周圍封到死」的來源。
   換成結構判定後（§1.1），**方向數量不再有任何上界**。
2. **`comp_path` 把端點凍結在一般階段。** 依賴路徑 `Path (B i) (a i) (b i)`
   的端點隨家族變動，舊程式在 `fam.at(DVar i)` 讀一次就當常數牆用，
   於是合成方向**洩漏進頂蓋**。症狀是複合路徑的纖維收縮的第一分量
   變成一坨 `glue` 而不是字面值。改成逐階段讀端點後，
   複合線上的收縮兩端都是定義等式（`general_wbtest.mbt` 的回歸測試）。

## 10. 效能：誠實的對照

`moon run --target native bench`，同一台機器：

| 項目 | 枚舉式 | 核心 `ctt` |
| --- | --- | --- |
| uaβ 窮舉 Fin 6（720 等價） | 14.19 ms | 37.69 ms（4320 次檢查） |
| `Fin 10^6` 上的傳輸 | 不可行 | **8.54 µs／次** |
| `1000^1000` 函式空間中的合成 | 不可行 | `O(1)`，結果 `#21` |
| 餘纖維蘊涵，2 方向（n=6） | 279.5 µs／次（`3^6`） | **0.57 µs／次**（**490×**） |
| 餘纖維蘊涵，200 文字、方向 5000+ | **跑不動**（`3^5200`） | **783 µs／次** |

最後兩列是本輪的重點。舊的蘊涵判定不是「比較慢」，而是**在核心真的需要它的地方完全無法執行**：
方向從 100 起跳，`3^100` 已經不可能枚舉。結構判定把這個上界整個拿掉。

**核心在小型別上仍然比較慢**——閉包配置是常數因子開銷。
它換到的是**漸近行為**：代價隨型別語法樹成長，而不是隨元素個數成長。
枚舉版留下來只當測試 oracle，因為它能回答「填充唯一嗎」。

---

## 11. 全代碼健檢

新增 `scripts/health.py`：以名字為基礎的死碼掃描 + 正規化函式體的重複偵測 +
套件行數統計。它是保守的（每個命中都應由人讀過再刪），
目的是讓「什麼沒被用到？」成為一條命令，而不是一次考古。

### 11.1 去重

發現 **6 份完全相同的整數次方**，散落在
`algebra/voa.mbt`、`algebra/einfty.mbt`、`cubical/cubety.mbt`、
`homotopy/nerve.mbt`、`deform/hochschild.mbt`、`omega/weak.mbt`，
外加 `nbe/symbolic.mbt` 的 `ipow2`。

全部收攏到 **`core/arith.mbt`** 的 `ipow` / `ipow2`，七處定義刪除，
所有呼叫點（含白箱測試）改為 `@core.ipow`。`omega` 與 `nbe` 補上 `core` 匯入。

刻意**不**用快速冪：每個呼叫點都在為列舉算尺寸（`n^k` 個胞、`d^{n+1}` 個餘鏈），
指數很小，而 `Int32` 溢位時的中間值順序必須與呼叫者的預期一致。

### 11.2 清死碼

初次掃描 **31 個從未被引用的函式**。處理方式是**分流**，不是一律刪除：

* **23 個表達了真實定理或有用 API** → 為它們補上執行測試，
  新增 13 個 `api_wbtest.mbt`（algebra、core、cover、deform、demorgan、
  derived、fiber、homotopy、nbe、omega、operad、rewriting、cubical）。
  死碼變成被驗證的碼。例如：
  * `e_word_count(r, 0) = r!`（surjection operad 的 Σ-自由性）
  * `e_word_count(1, d) = 0` for `d ≥ 1`（一元字母表上更長的字必退化）
  * `fills_inner_horns_2`：單體 fills，圓不 fills（Kan 條件）
  * `transport_along` 的函子性（窮舉 Z/3）
  * `normalize_closed`：β、算術、條件式化簡為字面值
  * `BoolMat::column` = 轉置的列
* **5 個是重復或瑣碎的** → 刪除：
  `core::nullity`（`ncols - r`）、`ctt::id_equiv`（被 `equiv_id` 取代）、
  `ctt::Tube::subst_dir`（未使用）、
  `cubical::dim_subst_endpoint` / `cof_subst_endpoint`（通用代入的特例）。
* **3 個新寫的 API** → 讓測試真的用它們（`ua_beta`、`tube_const`），
  而不是留著當裝飾。

結果：**死碼 0、重複函式體 0**。

### 11.3 減債：警告 70 → 0

* **44 條 `implicit_impl_as_method`**（`#derive` 隱式把 `to_repr`/`equal`
  提升為普通方法，已被標記為將來會移除）。
  從編譯器自己給的建議生成 **7 個 `extends.mbt`**，
  每個套件一份，顯式宣告 `pub extend T with Debug::{to_repr}` 等。
* **17 條 `unused_value` / `unused_type_declaration`**：
  `using` 區塊中未使用的名字（`deform`、`demorgan`、`fiber`、`ctt`），全部移除。
* **1 條 `unused_package`**：`demorgan` 不再需要 `rewriting`，移除匯入。
* **4 條未使用的 `self` 接收者**（`deform/artin.mbt`）→ `_self`。
* **1 條 `deprecated`**：`Option::or` → `unwrap_or`。
* **1 條 `unused_constructor`**：`Val` 的構造子只在測試中使用——
  這暴露了真正的 API 缺口：套件外無法建構型別。
  把 `Val` 改為 `pub(all) enum`，`Clo`/`DClo`/`Fam`/`Tube`/`Equiv` 等
  改為 `pub(all) struct`。核心現在可以從別的套件使用（`bench` 就是這樣用的）。

### 11.4 健檢前後

| | 前 | 後 |
| --- | --- | --- |
| 測試（wasm / native） | 136 / 136 | **188 / 188** |
| `moon check` 錯誤 | 0 | 0 |
| `moon check` 警告 | 61 | **0** |
| 死碼 | 22（舊掃描）／31（新掃描） | **0** |
| 重複函式體 | 6 份 `ipow` | **0** |
| 套件數 | 17 | **18** |

---

## 12. 檔案地圖

| 路徑 | 內容 |
| --- | --- |
| `ctt/value.mbt` | 值、閉包、型族、管壁、智能構造子、有界出現檢查、`memo_dclo`/`memo_fam`、`Nat`/`vsplit`/`vnatrec`、`fin_fun` |
| `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` | 雙向 Kan 運算：`interp`、`coe_between`、`comp_between`、`fill_between`、`transp`、`transp_path` |
| `ctt/symmetry.mbt` | 內部對稱：`cof_rev`、`Tube::rev`、`comp_rev`/`comp_sym` 等變、`sym_equiv`、`ua_sym` |
| `ctt/kan.mbt` | `comp` 分節（含 HIT）、`fill`、`coe`、`comp_glue` 一般条款、`unglue_cap` |
| `ctt/equiv.mbt` | `Contr`、`Equiv`、`equiv` 運算、`contr_iso`、`equiv_id/comp/inv`、惰性記憶 cell |
| `ctt/transport.mbt` | `transport_beta`（一次合成的來回）、`fiber_line`、`transport_center`、`transport_contr` |
| `ctt/univalence.mbt` | `ua`、`idtoeqv`、路徑代數、`funext`、`pathJ`、h-層級碼 |
| `ctt/hlevel.mbt` | `contr_path_contr`（二維盒子）、`prop_to_contr`、`is_prop_to_set` |
| `ctt/hit.mbt` | `S¹`、`Susp`、`∥A∥`、`Coeq`、形式合成、四個消除器、`trunc_is_prop`、`circle_trunc_contr` |
| `ctt/conv.mbt` | **無界**結構轉換、共享探測、η、等價的命題無關比較 |
| `ctt/quote.mbt` | 讀回渲染（只用於印）、quote-local 命名供應、維度與餘纖維渲染 |
| `ctt/*_wbtest.mbt` | 96 條定理 |
| `cubical/faces.mbt` | 結構蘊涵：DNF、join-primeness、稀疏 Kleene 求值、線性合併快路徑 |
| `cubical/interval.mbt` | 通用維度與餘纖維代入、`mentions`、`3^n` oracle（僅測試） |
| `core/arith.mbt` | 共用的 `ipow` / `ipow2` |
| `*/extends.mbt` | 7 份顯式 trait 方法提升 |
| `*/api_wbtest.mbt` | 13 份 API 表面測試 |
| `scripts/health.py` | 死碼／重複／行數掃描 |

---

## 13. 高階歸納型別

HIT 由點構造子**與路構造子**生成，而它的 Kan 結構還需要一樣東西：
**形式合成**。`S¹` 裡一個牆是 loops 的盒子，其頂蓋不在構造子之中，
所以頂蓋是一個新的形式項 `hcomp`，而每個消除器都要有對應的分節。
這正是 cubical Agda 讓 HIT 纖維化的方式，也是 `S¹` 不會塌成集合的原因。

| 型別 | 點構造子 | 路構造子 |
| --- | --- | --- |
| `S¹` | `base` | `loop : Path base base` |
| `Susp A` | `north`, `south` | `merid : A → Path north south` |
| `∥A∥` | `inc : A → ∥A∥` | `sq : Π x y. Path x y` |

三個消除器都**顯式帶著目標型別**：形式合成分節要把牆的像合成到那個型別裡，
而 HIT 消除器不是由點像 alone 決定的。

### 13.1 分節的意義

* 點構造子 → 給定的資料。
* 路構造子 → 給定的**路徑**，所以 β 規則**當場成立**，不是再差一個同倫。
  `ap (S¹-rec b l) loop = l` 是定義等式。
* 形式合成 → 牆的像的合成。這是**被迫的**：消除器要成為從 Kan 複形出來的
  函式，就必須保持合成。沒有這一分節，消除器在頂蓋上根本沒有定義。
* 中性元 → 停住。

### 13.2 證到的定理

* **`isProp ∥A∥`**：直接讀出路構造子。截斷就是 `A` 上的自由命題。
* **截斷的萬有性質**：目標 `B` 是命題時，`f : A → B` 唯一延拓成 `∥A∥ → B`。
  路構造子的分節是被迫的——`sq x y` 必須送到 `rec x` 到 `rec y` 的路徑，
  而 `B` 是命題恰好給出唯一一條 `prop (rec x) (rec y)`。
  它的**合法性本身就是目標必須是命題的理由**：一般的 `B` 沒有這條路徑。
* **`∥S¹∥` 可縮**： inhabited 的命題可縮，中心 `inc base`、收縮 `sq`。
  再餵給 §6 的 Hedberg 步，得到 `∥S¹` 是集合。
* **`S¹` 不是集合層級**：`loop ≠ refl`，而且牆不同的兩個形式合成不被判定相等，
  遞歸到 `S¹` 自身後仍然分得開。這一條是**負向**的，
  專門防止實作偷偷把 HIT 塌掉。

### 13.3 沒做的

`S¹` 的**普遍覆疊**（從而 `π₁(S¹) ≅ ℤ`）沒有寫：那需要一個無界整數型別
與 `S¹ → U` 的編碼，`VNat` 只有非負半边。
`circle_connected`（`Π x. ∥Path base x∥`）也沒有寫：
它的 loop 分節需要「命題家族上的依賴路徑」引理，
而那個引理要用 `isProp → isSet'` 的方形填充。
兩者都是誠實的缺口，不是已證的結果。

---

## 14. 雙向與內部對稱：Kan 運算的完整結構

`kan.mbt` 的 `comp` / `fill` / `coe` 由階段 `0` 走到 `1`。
那足以陳述單值性，但**唔係**立方集真正有嘅結構：區間係一個區間物件，
每個運算都定義喺**任意兩個階段** `r`、`r'` 之間，兩個方向都得，而且對兩者都自然。

本節嘅九個結構全部有實作、有測試：

| 要求 | 實作 | 檔案 |
| --- | --- | --- |
| 傳輸 | `transp`（帶餘纖維邊條件）、`transp_between`、`transp_path` | `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` |
| 投遞 | `coe_between`（`coe^{r→r'}`，任意兩階段） | `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` |
| 異質合體 | `comp_between`（型別沿方向變動）、`hcomp_const` 為常值特例 | `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` |
| 填充 | `fill_between`、`hfill_const`——由合成導出，唔係第二個原語 | `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` |
| 反轉操作 | `dim_not`、`cof_rev`、`Tube::rev`、`Fam::rev`、`path_sym`、`comp_rev`、`fill_rev` | `ctt/symmetry.mbt` |
| 高階歸納型別 | `S¹`、`Susp`、`∥A∥`、**`Coeq`**，含形式合成 `hcomp` | `ctt/hit.mbt` |
| 內部對稱立方類型論 | 每一層對 `~` 封閉，且 Kan 結構對 involution **等變** | `ctt/symmetry.mbt` |
| 雙向立方類型論 | 插值線 + 對角正則律 | `ctt/ua_eta.mbt` | `uaη` 對任意路徑：基礎 `Glue` 方形 + 路徑歸納 |
| `ctt/kan_ops.mbt` |
| 計算性單值性 | `uaβ` 對任意型別嚴格；全鏈用雙向／對稱運算再驗一次 | `ctt/computational_wbtest.mbt` |

### 14.1 插值線：一個裝置導出全部雙向運算

```text
interp(r, r', i) = (r ∧ ~i) ∨ (r' ∧ i)
```

`i = 0` 時係 `(r ∧ 1) ∨ (r' ∧ 0) = r`；`i = 1` 時係 `(r ∧ 0) ∨ (r' ∧ 1) = r'`。
所以佢係一條端點為 `r`、`r'` 嘅**維度項**，只用兩條聯絡同反轉就寫得出。
沿住佢重新索引家族，「由 `r` 到 `r'`」就變成「由 `0` 到 `1`」，
而後者有向核心已經識做：

```text
coe^{r→r'} A a = comp^i (i ↦ A(interp(r,r',i))) [] a
```

兩個特例**定義上**還原成原有運算，靠嘅係 `dim_and`/`dim_or` 嘅常數折疊：

* `interp(0,1,i) = i`，所以 `coe^{0→1} = coe`；
* `interp(1,0,i) = ~i`，所以 `coe^{1→0} = coe_back`。

### 14.2 對角正則律：De Morgan 同 Cartesian 嘅真正分界

`coe^{r→r} A a = a` 要求**嚴格**成立。留意插值線自己**畀唔到**呢條：

```text
interp(r,r,i) = (r ∧ ~i) ∨ (r ∧ i) ≠ r
```

因為自由 De Morgan 代數入面 `~i ∨ i ≠ 1`。呢一點正正係
De Morgan 區間同 Cartesian 區間嘅分界：Cartesian 立方集有**對角餘纖維**
`r = s`，正則律靠喺對角上放常值牆得到。本核心嘅餘纖維格只有端點面，
所以對角係喺合成**之前**用 `dim_eq` 判定。

結果係：**端點相等時正則律嚴格**；兩個唔同變元之間嘅對角**面**上，
正則律係命題式而唔係定義式。呢個分別係誠實嘅，唔係收埋咗。

### 14.3 `transp` 嘅邊條件係類型要求，唔係裝飾

```text
transp^i A φ a = comp^i A [φ ↦ a] a
```

牆係常值線 `i ↦ a`，所以佢合法**當且僅當** `A` 喺 `φ` 上係常值：
`φ ⊢ A(i) = A(0)`。沿 `ua` 線（喺任何非空面上都唔係常值），
只有 `φ = ⊥` 係合法嘅。兩個推論即時而且係定義式：

* `φ = ⊤`：管壁全覆蓋，結果就係 `a`；
* `φ = ⊥`：空管壁，`transp` 即 `coe`。

### 14.4 內部對稱 = Kan 結構對 involution 等變

淨係有 `~` 唔算「內部對稱」。要嘅係**每一層都對佢封閉，而且封閉係一個運算**：

| 層 | 反轉 | 律 |
| --- | --- | --- |
| 維度 | `dim_not` | `~~r = r`、`~(r∧s) = ~r∨~s` |
| 餘纖維 | `cof_rev` | `(r=e) ↦ (r=1-e)`，格自同構 |
| 家族 | `Fam::rev` | `A(~~i) = A(i)` |
| 管壁 | `Tube::rev` | 牆反轉、面反轉 |
| 合成 | `comp_rev` | 反向盒嘅頂蓋 |
| 路徑 | `path_sym` | `sym (sym p) = p`（定義式） |
| 等價 | `equiv_inv` | `(e⁻¹)¹ = e` |
| 單值性 | `ua_sym` | `ua(e⁻¹)` 同 `sym(ua e)` 傳輸相同 |

**等變律**係當中嘅核心，兩條推導必須一致：

1. **雙向**：`comp^{1→0}`，即沿 `interp(1,0,i) = ~i` 重新索引；
2. **對稱**：反轉家族、反轉管壁、反轉面，正向合成——
   `comp^i (A ∘ ~) [~φ ↦ u ∘ ~] a₀`。

`comp_rev` 同 `comp_sym` 喺 `Fin 4` 全部 24 個置換、每個 4 個起點上逐一相等。
呢個就係「Kan 結構對 involution 等變」嘅可執行陳述。

### 14.5 單值性嘅對稱性係定理，唔係折疊

`ua(e) = Glue [(i=0) ↦ (A,e), (i=1) ↦ (B,id)] B`。
反轉佢會換咗邊一端帶 `e`；而 `ua(e⁻¹) = Glue [(i=0) ↦ (B,e⁻¹), (i=1) ↦ (A,id)] A`。
**底唔同、分支資料唔同**，所以兩條線**唔係**定義相等——
測試明確 assert 佢哋喺一般階段 `val_conv` 為 `false`。
但端點相同、對 `B` 每一點嘅傳輸相同。所以對稱性係關於構造嘅定理。

### 14.6 計算性單值性：全鏈再驗一次

`computational_wbtest.mbt` 用**新**運算跑晒成條鏈：

* `Fin 4` 全部 24 個置換 × 4 點 × 5 種運算
  （`coe`、`coe_between`、`transp`、`transp_between`、反向）全部等於 `e.fwd`／`e.bwd`；
* `idtoeqv ∘ ua = id`（等價本身還原，唔止作用）；
* `ua ∘ idtoeqv = id` 喺 `ua` 像上，用無界結構轉換；
* **非嚴格**等價（`Fin 9` 複合線）：`equiv` + 修正方形，傳輸照樣計，
  纖維收縮兩端定義相等；
* **無限型別**：Cantor 空間 `Nat → Fin 2` 共軛 by negation，
  雙向都計，`nat_lit(100000)` 上一樣 `O(1)`，全程冇枚舉；
* 三段 `ua` 複合嘅函子性，同反向複合還原；
* `transp_path` 把 coercion 包成 `PathP`，於是 `sym`/`ap`/`J` 全部適用。

### 14.7 新增 HIT：餘等化子

`Coeq f g`（`f, g : A → B`）係 `B` 加上每個 `a : A` 一條
`rel a : Path (inc (f a)) (inc (g a))`。佢係每個集合商嘅原材料。

同按關係取商唔同，餘等化子**加路徑而唔截斷**：
`Coeq f f` 係 `B` 喺每個 `f a` 處加一個**圈**，唔係 `B` 本身。
所以核心必須保持 `rel a ≠ refl`——測試明確守住呢一條，
同時守住 `inc #0 ≠ inc #1`（餘等化子唔係集合截斷，
塌咗佢就係唔健全）。

消除器：要定義 `Coeq f g → C`，畀 `h : B → C` 同
`p : Π a. Path C (h (f a)) (h (g a))` 就夠；路構造子分節被迫係 `p a`，
所以 β 規則當場成立。

### 14.8 代價：一般性唔使畀錢

`moon run bench --target native`，`Fin 1000` 上嘅傳輸，2000 次：

| 運算 | µs／次 |
| --- | --- |
| `coe^{0→1}`，有向 | 7.07 |
| `coe^{0→1}`，經插值線 | **4.02** |
| `coe^{r→r}`，對角嚴格恆等 | **0.073** |

雙向版本**快過**有向版本，因為 `fam_between` 用 `memo_fam` 包過，
重新索引嘅家族只計一次；有向 `coe` 每次重新探測。
對角情形基本上唔使錢——`dim_eq` 判完就返，冇合成。

等變檢查：`comp_rev = comp_sym` 喺 96 個盒（24 置換 × 4 起點）上全部成立。

### 14.9 呢一節新增嘅驗證

| 檔案 | 條數 |
| --- | --- |
| `ctt/ops_wbtest.mbt` | 11 |
| `ctt/symmetry_wbtest.mbt` | 10 |
| `ctt/ua_eta_wbtest.mbt` | 8 | `uaη` 基礎方形、`refl`（像之外）、複合線、反向線、24 置換、路徑代數、單值性係等價、無限型別 |
| `ctt/computational_wbtest.mbt` | 8 |
| `ctt/hit_wbtest.mbt`（餘等化子部分） | +3 |

`ctt` 由 56 條增至 **88 條**，全庫 **254 條**，wasm 與 native 雙靶全綠。

---

## 15. `uaη`：最後一個缺口

要求：對**任意** `p : Path U A B`，構造

```text
uaη(p) : Path (Path U A B) (ua (idtoeqv p)) p
```

之前只喺 `ua` 嘅像上成立（嗰度係定義等式）。而家對任意路徑都有見證。

### 15.1 點解唔可以直接寫個方形

最自然嘅嘗試係

```text
Q(j,i) = Glue [ (i=0) ↦ (A, id), (i=1) ↦ (B, id), (j=0) ↦ (q(i), id) ] (p i)
```

（`q = ua (idtoeqv p)`）。四個面啱啱好係想要嘅嘢，但 `(j=0)` 分支需要
`Equiv (q i) (p i)`——**即係要證嘅嘢本身**。循環。

另一個嘗試係用 `fill` 造方形，再修正遠邊：遠邊
`R(j) = comp^i U [(j=0) ↦ q(i), (j=1) ↦ p(i)] A`
喺 `j=0`、`j=1` 都係 `B`，但一般 `j` 上係 `Glue`。要收回常數 `B`
就要一條 `S(j) : Path U (R j) B` 而且 `S(0)=S(1)=refl B`，
即係要證明 `R` 呢條圈係零倫——而且每個試寫嘅 `Glue` 都喺
`(j=0) ∧ (l=…)` 呢個重疊面上要求 `A = B`，唔合法。

### 15.2 用路徑歸納，而唔係直接造二維方形

對 `p` 做路徑歸納（固定 `A`，讓 `B` 同 `p` 一齊變）：

```text
mot(B, q) = Path (Path U A B) (ua (idtoeqv q)) q
```

淨返基礎情形 `B = A`、`p = refl A`。嗰度
`idtoeqv (refl A)` 兩個映射都係恆等——正則律令常值線上嘅 `coe`
**當場**係恆等——所以目標變成

```text
ua (id_A)  ~  refl A
```

### 15.3 基礎情形：所有分支資料相同嘅 Glue 方形

```text
D(j,i) = Glue [ (i=0) ↦ (A, id), (i=1) ↦ (A, id), (j=1) ↦ (A, id) ] A
```

**每個分支帶同一個型別、同一個等價**，所以重疊面上嘅相容條件自動成立。
呢個就係整個技巧，亦係點解基礎情形唔需要任何 coherence 資料。

* `j = 1`：嗰個面全覆蓋，`Glue` 塌成 `A`；線係常值，即 `refl A`。
* `j = 0`：嗰個面係空，剩返
  `Glue [(i=0) ↦ (A,id), (i=1) ↦ (A,id)] A = ua (id_A)`。
* `i = 0`、`i = 1`：全覆蓋，所以每條線兩端都係 `A`，圈應該係咁。

留意呢個**唔係** `Glue` 嘅正則律：`Glue [φ ↦ (A,id)] A` 唔係定義上嘅 `A`，
我哋亦冇假裝係。個方形係兩個**唔同**型別之間嘅真路徑，
只不過因為所有面一致所以易寫。
測試明確守住 `ua(id_A) ≠ refl A`（`val_conv` 為 `false`）。

### 15.4 歸納步，同點解兩端係定義等式

`pathJ(mot, D, p)` 係沿單點收縮嘅 `coe`，所以見證係**計出嚟**嘅。
而路徑型別嘅合成將兩個端點放入**管壁**：
`comp_path` 嘅結果喺 `j=0` 時 `(j=0)` 分支全覆蓋，
`total_tube` 直接傳回嗰道牆。所以

```text
uaη(p) @ 0  ≡  ua (idtoeqv p)      uaη(p) @ 1  ≡  p
```

**兩端都係定義等式**，唔係「差一條路徑」。

### 15.5 驗證（8 條，`ctt/ua_eta_wbtest.mbt`）

| 情形 | 檢查 |
|---|---|
| 基礎方形 | `j=0` 得 `ua(id)`、`j=1` 得 `refl`；每條線兩端係 `A`；**`ua(id) ≠ refl`** |
| `p = refl A` | **喺 `ua` 像之外**：兩端 `val_conv` 為 `false`，見證兩端仍然定義相等 |
| 複合線 `ua(e)·ua(e)` | 兩端唔同，見證兩端定義相等；每條線兩端係 `Fin 5` |
| 反向線 `sym(ua e)` | 兩端定義相等；傳輸係逆置換 |
| `Fin 4` 全部 24 個置換 | 像上退化為定義等式，見證仍然構造得出 |
| 路徑代數 | `sym`、`concat` 對見證適用；兩端嘅傳輸一致 |
| **單值性係等價** | `uaβ`（定義）+ `uaη`（構造）合起來即 `ua` 同 `idtoeqv` 互逆 |
| 無限型別 | Cantor 空間 `Nat → Fin 2`，同一個 `J`，冇枚舉 |

`ctt` 由 88 條增至 **96 條**，全庫 **262 條**，wasm 與 native 雙靶全綠。

### 15.6 而家冇剩低嘅缺口

`uaβ` 對任意型別嚴格；`uaη` 對任意路徑有構造見證；
一般（非嚴格）等價嘅 `Glue` 合成有 `equiv` 同修正方形；
Hedberg、HIT、無界轉換、中性完備離散函式、雙向同內部對稱結構全部有埋。
