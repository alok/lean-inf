# Whiteboard Talk Guide — `lean-inf` at Theorem

**Title**: *Inf: Making Infinities and Infinitesimals First-Class, Computable, and Verified-Fast in Lean 4*  
**Format**: 25–30 min whiteboard talk + live calculator demo + Q&A  
**Repo**: `~/lean-inf` (`github.com/alok/lean-inf`)  
**Live Demo**: `http://127.0.0.1:4420/` (and blog `/inf/` backed by `https://mac.tailbf1ac1.ts.net/inf-api`)

---

## 30-Second Elevator Pitch

Instead of treating $\infty$ as an algebraic dead end—or escaping to heavy Schwartz distribution theory to differentiate a step function—we enlarge the number system with one unlimited constant **$H$** and its infinitesimal reciprocal **$\varepsilon = 1/H$** using the **Levi-Civita field** in Lean 4. We get automatic differentiation (even of discontinuous functions like the Heaviside step $\to$ Dirac delta!) for free, and we use Lean 4 for **zero-`sorry` verified refactoring**: proving Karatsuba multiplication ($O(n^{1.585})$), $O(1)$ sign, binary exponentiation, and quadratically convergent Newton inversion equivalent to the naive baseline, yielding **5.8×–311× measured native speedups**.

---

## Whiteboard Layout Plan (3 Panels)

```
┌───────────────────────────┬───────────────────────────────┬───────────────────────────────┐
│  LEFT BOARD: WHY & WHAT   │  CENTER BOARD: STEP → DELTA   │  RIGHT BOARD: VERIFIED FAST   │
│                           │                               │                               │
│  H (discrete hypernat!)   │  L_H(x) = 1 / (1 + e^{-Hx})   │  Naive HashMap   →  FastLC    │
│  ε = 1/H (infinitesimal)  │  [Draw steep S-curve]         │  O(n²) mul       →  O(n^1.585)│
│                           │                               │  O(n log n) sign →  O(1)      │
│  Levi-Civita field:       │  H is CONSTANT in x!          │  O(k) pow        →  O(log k)  │
│  ∑ c_i H^{q_i}, q_i ∈ Q   │  L'_H(x) = H e^{-Hx}/(1+e)^2  │  O(N) inv        →  O(log N)  │
│                           │  [Draw tall narrow spike]     │                               │
│  Order by leading term:   │  x = 0:      L'_H(0) = H/4    │  Untrusted heuristic          │
│  ε² < ε < √ε < 1 < H < H² │  x = cε:     σ'(c) · H        │   + Verified grid checker     │
│                           │  x ≠ 0 std:  ≈ 0              │   + Verified Karatsuba        │
│  Why H ≠ ε subtly:        │  Area: ∑ σ'(c) H · (Δc·ε) = 1 │   + Verified mulTree fallback │
│  H ∈ *N → induction!      │                               │                               │
│  Discrete + Continuous    │  Finite eval: H ↦ N, ε ↦ 1/N  │  Newton: 1 - uy' = (1 - uy)²  │
│  = Hybrid systems         │  D_{ε²} L_H(0) = H/4 - ε/48…  │  O(ε^d) → O(ε^{2d})           │
└───────────────────────────┴───────────────────────────────┴───────────────────────────────┘
```

---

## Act-by-Act Script

### Act 1 — WHY (3 min)
1. **The classical annoyance**: Ask the room what the derivative of the Heaviside step function $U(x)$ is. Everyone says "Dirac delta $\delta(x)$." Ask how it's defined rigorously: *"an element of the continuous dual space of $C_c^\infty$ test functions."* That takes half of grad school just to state, and you still can't evaluate $\delta(0)$ as a number!
2. **The simpler move**: Look at history: $\mathbb{N} \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{R} \to \mathbb{C}$. Every time arithmetic failed ($3 - 5$, $x^2 + 1 = 0$), we didn't throw away functions—we **enlarged the numbers**. Here, $\frac{1 - 0}{0 - 0}$ fails only because $\mathbb{R}$ has no infinite or infinitesimal numbers.
3. **Add one constant $H$ (and $\varepsilon = 1/H$)**:
   - Unlike $\infty$, $H$ obeys ordinary algebra: $2H > H$, $H + 1 > H$, $H - \varepsilon > 0$, $H \cdot \varepsilon = 1$.
4. **The subtle insight about $H$ vs $\varepsilon$ (don't skip this!)**:
   - Even though $\varepsilon = 1/H$, **$H$ is conceptually a discrete quantity**—an infinitely large *whole number* (a hypernatural $H \in {}^*\mathbb{N}$).
   - In nonstandard analysis (Robinson / Nelson's IST), **you can do induction over $H$**.
   - Partitioning a continuous interval $[a,b]$ into $H$ slices of infinitesimal width $\Delta x = (b-a)/H = (b-a)\varepsilon$ turns integration into finite summation and gives **induction over continuous quantities**.
   - That lets a single formalism reason cleanly about continuous systems, discrete steps, and **hybrid systems** (part discrete, part continuous—like robotics, control, and physical simulation).

### Act 2 — WHAT (4 min)
1. **Why Levi-Civita instead of full Hyperreals on a computer?**
   - Robinson's hyperreals ${}^*\mathbb{R}$ use a non-principal ultrafilter (Axiom of Choice) — great for proofs, not directly computable.
   - Tullio Levi-Civita (1892) constructed a **computable** non-Archimedean real-closed ordered field: formal series with rational exponents (left-finite support):
     $$a = \sum_{i} c_i H^{q_i}, \qquad q_0 > q_1 > q_2 > \dots \in \mathbb{Q},\quad c_i \in \mathbb{Q}\text{ (or }\mathbb{R}\text{)}$$
   - **Analogy**: Levi-Civita is to Hyperreals as $\mathbb{Q}$ is to $\mathbb{R}$ (computable, ordered, exact arithmetic, captures algebraic + Taylor/analytic calculus; only super-polynomial growths like $e^H$ leave the field).
2. **Autodiff for free**:
   - For smooth $f$, $f'(x) = \text{st}\!\left(\frac{f(x + \varepsilon) - f(x)}{\varepsilon}\right)$ — no limits, no dual-number special casing, and higher orders come along automatically:
     $$\frac{(2+\varepsilon)^4 - 2^4}{\varepsilon} = 32 + 24\varepsilon + 8\varepsilon^2 + \varepsilon^3.$$

### Act 3 — WHITEBOARD CENTERPIECE: Differentiating the Step Function & Finite Evaluation (8 min)

**Draw Step 1 (Nonstandard Logistic Step)**:
- Classical dynamic view: $\lim_{N \to \infty} \frac{1}{1 + e^{-Nx}}$.
- Nonstandard static view: skip to the end—pick ONE unlimited constant $H$ and define:
  $$L_H(x) = \frac{1}{1 + e^{-H x}}.$$
- Draw the S-curve rising from $0$ to $1$ across an infinitesimal width $O(\varepsilon)$ around $0$, passing through $(0, 1/2)$. Appreciably indiscernible from the Heaviside step!

**Draw Step 2 (Differentiate by noticing $H$ is constant!)**:
- Point at $H$ on the board: *"$H$ is infinite, yes—but it is a **constant** with respect to $x$!"*
- Differentiate using plain Calc 1 chain rule:
  $$L'_H(x) = \frac{H e^{-H x}}{(1 + e^{-H x})^2}.$$
- **Case analysis across the 3 regimes**:
  1. **Appreciable $x \neq 0$** (e.g. $x = 1$ or $-1$): $H|x|$ is infinite, so $e^{-H|x|}$ decays faster than every $\varepsilon^k$ $\implies L'_H(x) \approx 0$.
  2. **Exactly $x = 0$**: $H \cdot 0 = 0$ (exact zero!). Thus:
     $$L'_H(0) = \frac{H \cdot e^0}{(1 + e^0)^2} = \mathbf{\frac{H}{4}}.$$
     *(Pause for the laugh! "How tall is the Dirac delta? Not vague $\infty$, specifically $H/4$!")*
  3. **Infinitesimal transition layer $x = c \cdot \varepsilon$**:
     Look at the exponent: $-H \cdot (c\varepsilon) = -c \cdot (H\varepsilon) = -c$ — **FINITE!!**
     So $L'_H(c\varepsilon) = \sigma'(c) \cdot H$ (at $c = 1$, $L'_H(\varepsilon) \approx 0.1966\,H$).
- **Check the area = 1 on the board**:
  $$\sum_k L'_H(c_k \varepsilon) \cdot (\Delta c \cdot \varepsilon) = \sum_k \sigma'(c_k) \underbrace{H \cdot \varepsilon}_{=\,1} \Delta c \;\longrightarrow\; \int_{-\infty}^{\infty} \sigma'(c)\,dc = 1.$$
  Height is $O(H)$, width is $O(\varepsilon)$, and $H \cdot \varepsilon = 1$ cancels algebraically!

**Draw Step 3 (How `lean-inf` differentiates $L_H$ purely via AD — NO hardcoded derivative!)**:
- Subtle catch if you try step size $\varepsilon$: $H \cdot \varepsilon = 1$ jumps across the entire transition layer!
- Fix: differentiate with a **second-order infinitesimal** $\eta = \varepsilon^2$! Then $H \cdot \varepsilon^2 = \varepsilon$ is STILL infinitesimal, so $e^{-c - \varepsilon} = e^{-c}\sum_{k \ge 0} \frac{(-\varepsilon)^k}{k!}$ converges inside the Levi-Civita field!
- Pure central difference quotient in `lean-inf`:
  $$D^{\text{sym}}_{\varepsilon^2} L_H(0) = \frac{L_H(\varepsilon^2) - L_H(-\varepsilon^2)}{2\varepsilon^2} = \frac{1}{4}H - \frac{1}{48}\varepsilon + \frac{1}{480}\varepsilon^3 - \frac{17}{80640}\varepsilon^5 + \dots$$
  Exact rational Bernoulli-tangent series, computed automatically by `StepFunction.logisticDerivCentral`!

**Draw Step 4 (Finite Evaluation / Relative Specialization: $H \mapsto N$)**:
- *"Okay, how do I plot this or plug it into a finite numerical code?"*
- Pick any finite surrogate $N > 0$ (e.g. $N = 100$ or $1000$) for the unlimited constant $H$, and plug everything else in **relative to $N$**:
  $$H \mapsto N, \qquad \varepsilon = H^{-1} \mapsto \frac{1}{N}, \qquad x = c\varepsilon \mapsto \frac{c}{N}, \qquad \text{evalFinite}\!\left(\sum_i c_i H^{q_i},\, N\right) = \sum_i c_i N^{q_i}.$$
- Concrete outputs from `lake exe inf step-demo --N 100`:
  - At $x = 0$: $\text{evalFinite}(D_{\varepsilon^2} L_H(0), 100) = 24.999792$ (exact $N/4 = 25.0000$).
  - At $x = \varepsilon \mapsto 0.01$: $\text{evalFinite}(D_{\varepsilon^2} L_H(\varepsilon), 100) = 19.661134$ (exact $N\sigma'(1) = 19.661193$).
  - Hyperfinite Riemann area across $c \in [-8, 8]$: `0.9994`!
- Show the generated plot (`plots/step_function_finite_eval.png`) or live slider in Tab 2!

---

### Act 4 — HOW: Verified Refactoring in Lean 4 (7 min)

**The Narrative**: *"I originally wrote the naive HashMap version of `lean-inf` just to get it working. Revitalizing it in Lean 4 gave us two wins at once: catching silent bugs in the original code, and doing verified refactors for speed without ever breaking semantics."*

1. **Two real bugs found in the original naive code**:
   - `Std.HashMap` `BEq` wrote `ys.getD k v == v`, which returned `true` whenever `k` was missing from `ys`!
   - `LeviCivitaNum.signum` sorted ascending (`exp₁ < exp₂`), reading the *smallest* infinitesimal instead of the dominant largest exponent (saying `H - ε < 0`!).
2. **Semantic Spec + Canonical Type (`FastLC`)**:
   - Denotational semantics: `coeffOf : TermList → Rat → Rat` (works on ANY unsorted/duplicate list!).
   - Canonical representation: `FastLC` = strictly descending nonzero `List (Rat × Rat)` carrying an erased `WF` proof (zero runtime cost!).
   - **Canonicality theorem** (`eq_of_wf_of_coeffOf_eq`): `WF a → WF b → (∀ e, coeffOf a e = coeffOf b e) → a = b`.
3. **The 5 Zero-`sorry` Verified Refactors (all `#print axioms` clean!)**:
   | Operation | Original Naive | Verified Fast Refactor | Headline Theorem (0 `sorry`) | Measured Speedup |
   |---|---|---|---|---|
   | `signum` | $O(n\log n)$ HashMap + `qsort` | $O(1)$ head lookup | `signumFast_eq_one_iff` | **311× – 540×** |
   | `add` / `sub` | HashMap + `filterZeros` | $O(n+m)$ two-pointer merge | `coeffOf_addMerge`, `addMerge_wf` | zero hashing |
   | `mul` (dense) | $O(n^2)$ nested HashMap | Verified **Karatsuba** $O(n^{1.585})$ | `dCoeff_dMulKaratsuba`, `coeffOf_mulFast` | **5.8×** ($n=512$) |
   | `mul` (sparse) | $O(n^2)$ nested HashMap | Balanced binary-tree `mulTree` | `coeffOf_mulTree`, `mulTree_wf` | **1.3×** ($n=64$) |
   | `pow` (`x^k`) | $O(k)$ linear loop | $O(\log k)$ binary squaring | `powFast_eq_powNaive` | **4.3×** ($k=48$) |
   | `inv` (`1/x`) | $O(N)$ geometric series | $O(\log N)$ **Newton-Raphson** | `newton_residual_squares`, `newton_order_doubles` | **13.8×** (ord=40) |
4. **Two Whiteboard Jewels for a Lean-Savvy Audience**:
   - **Jewel A — Untrusted Heuristic + Verified Checker Pattern for Karatsuba**:
     Arbitrary Levi-Civita numbers can have messy rational exponents ($H^{3/2} + \varepsilon^{1/3}$), whereas Taylor series live on a regular grid $e_0 - k\Delta$. We guess $\Delta$ with an *untrusted* heuristic, run a linear-time *verified checker* (`extractGridAux_sound`), run *verified Karatsuba* (`dCoeff_dMulKaratsuba`), and fall back to *verified `mulTree`* if off-grid. The top-level theorem `mul_eq_mulNaive` doesn't even care how the heuristic guesses $\Delta$!
   - **Jewel B — Quadratic Valuation Doubling for Newton Inversion**:
     Write two lines on the board:
     $$1 - u \cdot \big(y(2 - uy)\big) = (1 - uy)^2$$
     $$\text{AllLe}(-d,\; 1 - uy) \;\implies\; \text{AllLe}(-2d,\; 1 - u \cdot \text{newtonStep}(u, y)).$$
     Every Newton iteration literally **doubles** the order of infinitesimal accuracy!

---

### Act 5 — Live Demo Script (3 min)

Open `http://127.0.0.1:4420/` (or blog `/inf/`), point to the green **`Lean 4.36.0 · Live`** badge:
1. Type `[(2 + ε)^4 - 2^4] / ε` → `32 + 24ε + 8ε² + ε³` (0.2ms, standard part `32`).
2. Type `dstep(0)` → `(1/4)H - (1/48)ε + (1/480)ε³ - ...` (2ms, dominant `(1/4)H`, `H ↦ 100` = `24.9998`).
3. Type `dstep(ε)` → `0.1966H - ...` and `dstep(1)` → `0`.
4. Switch to **Step Function → Dirac Delta (H ↦ N)** tab:
   - Drag the $N$ slider from `10 → 40 → 100 → 250`. Watch the step sharpen, the Dirac delta peak climb to `N/4` while hyperfinite area stays `≈ 1.000`, and Lean 4 `evalFinite(N)` dots sit dead-on the analytic curve!
   - Drag the $c$ probe to `c = -1`, `0`, `+1` to show the exact symbolic Levi-Civita expression inside the infinitesimal layer!
5. Switch to **Verified Refactors & Benchmarks** tab to show the zero-`sorry` theorems and live benchmark table.
6. Optional terminal flex: run `lake exe inf test` (`122/122 passed`) and `#print axioms LeanInf.Karatsuba.coeffOf_mulFast`.

---

## Anticipated Tough Q&A (from Theorem Engineers & Mathematicians)

1. **"Wait—isn't $\exp(H)$ outside the Levi-Civita field? How does $L_H(x) = \frac{1}{1+e^{-Hx}}$ work?"**
   - Great catch! Yes: $e^H$ grows faster than every rational power $H^q$, so `exp(H)` rightly returns an error in the calculator.
   - Inside the **infinitesimal transition layer** $x = c\varepsilon + O(\varepsilon^2)$, the product $-Hx = -c + O(\varepsilon)$ is **finite**, so $e^{-Hx} = e^{-c} \sum \frac{(O(\varepsilon))^k}{k!}$ converges *inside* the Levi-Civita field!
   - For appreciable $x \neq 0$, $e^{-H|x|}$ is super-exponentially infinitesimal ($< \varepsilon^k$ for all $k$), which vanishes to every polynomial Levi-Civita order (giving $L_H(x) = 1$ for $x>0$, $0$ for $x<0$). That distinction is literally the boundary between Levi-Civita fields and full Robinson hyperreals / Hardy transseries.

2. **"Why did you differentiate $L_H$ with step $\varepsilon^2$ instead of $\varepsilon$?"**
   - Because the transition width of $L_H$ is *itself* $O(\varepsilon) = O(1/H)$! Stepping by $\Delta x = \varepsilon$ jumps across the whole cliff ($H\Delta x = 1$, finite secant slope, not tangent!). Stepping by $\eta = \varepsilon^2$ gives $H\eta = \varepsilon \ll 1$, so the perturbation stays infinitesimal relative to the cliff width!

3. **"Why didn't your benchmark use `Float` / SIMD if you care about speed?"**
   - Two reasons: (i) exact `Rat` coefficients let us prove **exact algebraic equality** (`mul_eq_mulNaive`, `powFast_eq_powNaive`, `newton_residual_squares`) with zero floating-point rounding caveats, and (ii) Karatsuba's speedup ($O(n^{1.585})$ vs $O(n^2)$) is actually *more* dramatic on exact `Rat` where each scalar multiply costs GCD reduction. A great next step is a `FloatArray` backend verified up to floating-point error bounds (or exact fixed-precision integer mantissas).

4. **"Your benchmarks ran in a loop—how do you know Lean didn't hoist or dead-code-eliminate them?"**
   - We caught that exact LICM/CSE artifact on our first benchmark run! We fixed it with `@[noinline]` wrappers, an 8-element pool of distinct prebuilt inputs indexed by the loop counter `i % 8`, warmup passes, and an observable checksum—and verified the empirical doubling ratio: Naive scales $3.97\times$ per doubling ($\approx 2^2$), Karatsuba scales $2.91\times$ ($\approx 2^{1.585} = 3$).

5. **"How does `H` being discrete actually help with hybrid systems?"**
   - In hybrid control (discrete mode switches + continuous ODE flow), you normally need separate formalisms (automata + differential equations). With a hypernatural $H \in {}^*\mathbb{N}$ and $\Delta t = 1/H = \varepsilon$, continuous evolution *is* a hyperfinite discrete loop of $H$ steps $x_{k+1} = x_k + f(x_k)\varepsilon$ ($k = 0, \dots, H-1$). Discrete mode guards and continuous trajectories live in the exact same inductive loop!

6. **"Can `lean-inf` compute higher-order derivatives or multivariate gradients?"**
   - Higher-order: yes—already demonstrated with `ddstep` ($L''_H$ dipole) via second differences, and Taylor coefficients of `f(x + ε)` directly read off *all* derivatives $f^{(k)}(x) / k!$ simultaneously in one forward pass!
   - Multivariate: using linearly independent/commensurate infinitesimal scales (e.g., $\varepsilon$, $\varepsilon^{1/p}$, or sparse multi-index exponents) or lifting tensors as in `~/infnum`.

7. **"What broke when converting exact rational Levi-Civita results to floats in `evalFinite`?"**
   - Great war story: summing 65 exact rationals with $10^{10}$ denominators in the hyperfinite Riemann integral caused the exact LCM denominator to exceed $2^{1024}$ ($\sim 10^{308}$), turning `Float.ofNat num / Float.ofNat den` into `Inf / Inf = NaN`! Fixing `ratToFloat` with `Nat.log2` bit-shift normalization + `Float.scaleB` made `evalFinite` overflow-proof for arbitrarily large exact rationals.
