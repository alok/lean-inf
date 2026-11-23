import Foundation

enum SlideVisualKind {
    case titleHero
    case continuumCut
    case stepToDirac
    case firstTriesTimeline
    case speedupBars
    case grindAndFloatLib
    case verificationPillars
    case liveDemoLauncher
}

struct SlideDemoAction: Identifiable {
    let id = UUID()
    let title: String
    let subtitle: String
    let expr: String?
    let clearForPencil: Bool
}

struct SlideNotes {
    let broadStroke: String
    let microdetails: [String]
    let cutIfBehind: String
    let expandIfAhead: String
    let paceAnchor: String
}

struct QACheatItem: Identifiable {
    let id = UUID()
    let question: String
    let answer: String
}

struct InfSlide: Identifiable {
    let id: Int
    let startTime: String
    let gateTime: String
    let gateSeconds: Int
    let title: String
    let thesis: String
    let visual: SlideVisualKind
    let microdetails: [String]
    let notes: SlideNotes
    let demoActions: [SlideDemoAction]
    let qaItems: [QACheatItem]
}

/// 8 top-down broad-stroke + sharp-microdetail slides in Alok's voice with clean math Unicode
/// (strictly zero em/en dashes, zero prose exclamation marks, zero semicolons, zero meta-words).
enum SlideDeck {
    static let targetSeconds: Int = 13 * 60

    static let slides: [InfSlide] = [
        // Slide 1 (index 0)
        InfSlide(
            id: 0,
            startTime: "0:00",
            gateTime: "0:30",
            gateSeconds: 30,
            title: "Inf: Computable Infinitesimals in Lean 4",
            thesis: "One verified infinite unit H with ε = 1/H lets Lean compute calculus, step functions, and Dirac deltas algebraically.",
            visual: .titleHero,
            microdetails: [
                "Core ring ℚ[H^ℚ] proved in zero-Mathlib Lean 4.36 with zero sorry",
                "Dense 512-term multiplication runs in 0.38 ms instead of 112.6 ms",
                "187/187 differential parity against exact rational oracle across 7 engines"
            ],
            notes: SlideNotes(
                broadStroke: "Open fast on the goal: make infinitesimals and infinities computable, fast, and kernel-checked in Lean 4 so continuous math looks discrete.",
                microdetails: [
                    "Define H as a formal infinite unit and ε = 1/H as an infinitesimal.",
                    "Everything you see today runs live in compiled Lean 4.36 behind this iPad."
                ],
                cutIfBehind: "Skip reading the three pills aloud and go straight to Slide 2.",
                expandIfAhead: "Note that the iPad app talks directly to compiled Lean 4 over Tailscale.",
                paceAnchor: "Leave Slide 1 by 0:30."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 2 (index 1)
        InfSlide(
            id: 1,
            startTime: "0:30",
            gateTime: "2:30",
            gateSeconds: 150,
            title: "Why enlarge the numbers",
            thesis: "Split [a, b] into H pieces of width ε = 1/H. Integrals become finite-looking sums and ODEs become H-step loops.",
            visual: .continuumCut,
            microdetails: [
                "Distributions work linearly, yet products like δ² break down",
                "Dual numbers enforce ε² = 0, so you cannot invert ε or take H = 1/ε",
                "Full hyperreals *ℝ need a non-principal ultrafilter, so Lean proves the computable ordered subring ℚ[H^ℚ] with division truncated to order"
            ],
            notes: SlideNotes(
                broadStroke: "Most proof engineering stays discrete because PL folks dislike floats and continuous math hides behind limits and distributions. Enlarging the number system turns continuous objects back into algebra.",
                microdetails: [
                    "Dual numbers are great for forward AD, yet ε² = 0 kills 1/ε and infinite heights.",
                    "ℚ[H^ℚ] is a computable ordered subring inside the Levi-Civita field, not a field, because (1+ε)⁻¹ has infinite support and truncates to a chosen order."
                ],
                cutIfBehind: "Mention only dual numbers vs ℚ[H^ℚ] and skip the ultrafilter remark.",
                expandIfAhead: "Draw [a, b] ticks with Apple Pencil to show H subintervals of width ε.",
                paceAnchor: "Hit Slide 3 by 2:30."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 3 (index 2)
        InfSlide(
            id: 2,
            startTime: "2:30",
            gateTime: "4:00",
            gateSeconds: 240,
            title: "Step function to Dirac delta",
            thesis: "Plug H into a smooth logistic Lₕ(x) = 1/(1 + exp(-H·x)). Calc 1 turns it into a Dirac delta of height H/4, width ε, and area 1.",
            visual: .stepToDirac,
            microdetails: [
                "Exact symbolic derivative gives Lₕ'(0) = H/4 with zero distribution theory",
                "Central difference must step by η = ε² because step ε jumps the cliff since H·ε = 1",
                "Pure AD prints dstep(0) = (1/4)H - (1/48)ε + (1/480)ε³ ..., where -(1/48)ε is the O(ε²) discretization tail"
            ],
            notes: SlideNotes(
                broadStroke: "Take 1/(1+exp(-H·x)). Macroscopically it looks like a Heaviside step, yet microscopically on ±8ε it is smooth and differentiable by ordinary algebra.",
                microdetails: [
                    "Be explicit before anyone asks: exact Lₕ'(0) = H/4, while central difference at step ε² outputs (1/4)H - (1/48)ε + ... from the O(ε²) difference quotient.",
                    "Tap the live jump button if you want a quick 15-second flash of the curve right now, or save the full demo for Slide 8."
                ],
                cutIfBehind: "Skip tapping live preview here and save all live calculator taps for Slide 8.",
                expandIfAhead: "Tap nonstd step, toggle Micro ±8ε, and scrub N from 10 to 1000.",
                paceAnchor: "Leave Slide 3 by 4:00."
            ),
            demoActions: [
                SlideDemoAction(
                    title: "Live nonstd step",
                    subtitle: "Plot 1/(1+exp(-H·x)) in Lean 4",
                    expr: "1/(1+exp(-Hx))",
                    clearForPencil: false
                )
            ],
            qaItems: []
        ),

        // Slide 4 (index 3)
        InfSlide(
            id: 3,
            startTime: "4:00",
            gateTime: "5:30",
            gateSeconds: 330,
            title: "2024 to 2026: Lean + AI evolution",
            thesis: "Hand-written unordered maps in Julia, Python, and Lean 4.10 hid silent bugs. Moving the invariant into Lean 4.36 closed the oversight gap.",
            visual: .firstTriesTimeline,
            microdetails: [
                "2022 Julia Dict and 2024 Python prototypes stayed unverified and accumulated 31 differential bugs",
                "Jul 2024 Lean 4.10 HashMap left TODO use RbMap and shipped silent BEq (H == H²) and ascending-sort signum (H - ε < 0) bugs",
                "Nov 2026 FastLC puts strictly descending TermList.WF in the type and swaps fast kernels via @[csimp]"
            ],
            notes: SlideNotes(
                broadStroke: "Compare real code from July 2024 commit 0088b08 against November 2026 VerifiedRefactor.lean. Putting TermList.WF in the type lets the Lean kernel close the oversight gap on aggressive AI rewrites.",
                microdetails: [
                    "Directly mirrors Theorem's oversight-gap thesis (lf-lean): AI proposes aggressive representation and algorithm rewrites, while Lean's kernel acts as the closed-loop oracle.",
                    "In July 2024, HashMap sorted keys ascending for signum (treating H - ε < 0) and BEq treated H == H² as equal."
                ],
                cutIfBehind: "Point only to the Jul 2024 HashMap TODO versus Nov 2026 FastLC WF structure.",
                expandIfAhead: "Highlight how the 187-case diff suite caught 25 bugs in 2024 Lean and 31 in 2024 Python.",
                paceAnchor: "Reach Slide 5 by 5:30."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 5 (index 4)
        InfSlide(
            id: 4,
            startTime: "5:30",
            gateTime: "8:00",
            gateSeconds: 480,
            title: "Verified optimization loop (climb-01..09)",
            thesis: "Every AI speedup (Karatsuba, Int Kronecker packing, Array Int Newton) had to prove equality to the naive spec before landing.",
            visual: .speedupBars,
            microdetails: [
                "Untrusted grid guess plus linear verified checker feeds Array Int Karatsuba/Kronecker on GMP",
                "5 literal @[csimp] lemmas swap slow verified loops for fast kernels in C IR, with 5 rejected runs logged",
                "Held-out OOD benchmarking caught the Axis-3 den != 1 gap and lean.h:1570 2^31-1 GMP cliff"
            ],
            notes: SlideNotes(
                broadStroke: "Once the invariant lives in the type, signum is O(1) at index 0 and dense 512-term multiplication drops from 112.6 ms to 0.38 ms while staying provably equal to mulNaive.",
                microdetails: [
                    "Every AI speedup (Karatsuba, Int Kronecker packing, Array Int Newton) had to prove equivalence to the spec before landing, and held-out OOD benchmarking caught the lean.h 2^31-1 GMP cliff.",
                    "Live cached bench table shows 296x dense mul (324x isolated), 425x inv (361x isolated), 13.9x sparse mul, and 636x signum."
                ],
                cutIfBehind: "Focus only on mul_dense (112.6 ms -> 0.38 ms) and mul_eq_mulNaive.",
                expandIfAhead: "Explain why 5 candidate optimizations were rejected when they regressed sparse cases or hit GMP packing cliffs.",
                paceAnchor: "Hit Slide 6 by 8:00."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 6 (index 5)
        InfSlide(
            id: 5,
            startTime: "8:00",
            gateTime: "9:30",
            gateSeconds: 570,
            title: "Lean 4.36 grind and isolated FloatLib stack",
            thesis: "Keep the computable core zero-Mathlib using Lean 4.36 grind, and isolate Mathlib and FloatLib IEEE-754 proofs in a separate bridge package.",
            visual: .grindAndFloatLib,
            microdetails: [
                "Core exports Lean.Grind CommRing and OrderedRing (not Field) with 23 GrindShowcase theorems and 32 by grind proofs",
                "Nested float-proofs/ builds 24 zero-sorry IEEE-754 theorems over FloatLib Binary64 without bloating core builds",
                "Certifies 24.99979 < v < 24.99980 on Binary64 Sum2 for 3-term dstep(0) at N=100, < 4 u64 sigmoidB64, and N = 2^60 cancellation separation"
            ],
            notes: SlideNotes(
                broadStroke: "Mirrors Theorem's Verified Software Stack pattern: keep the computable core zero-Mathlib and fast, and isolate Mathlib and FloatLib proofs in a separate bridge package.",
                microdetails: [
                    "Be precise for Rajashree: diracCenter_at_100_certified proves Binary64 Sum2 on the 3-term dstep(0) constant, separate from runtime Float.pow in FastLC.evalFinite.",
                    "At N = 2^60, FastLC keeps exact cancellation (FastLC 2 vs naive Float 0 vs Sum2 2)."
                ],
                cutIfBehind: "Point to OrderedRing FastLC + by grind on the left and 24 FloatLib theorems on the right.",
                expandIfAhead: "Walk through N = 2^60 cancellation separation: FastLC 2 vs naive Float 0 vs Sum2 2.",
                paceAnchor: "Reach Slide 7 by 9:30."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 7 (index 6)
        InfSlide(
            id: 6,
            startTime: "9:30",
            gateTime: "11:00",
            gateSeconds: 660,
            title: "Verification surface and 77 benchmarks",
            thesis: "Proofs cover the algebraic kernel, while a 7-engine differential suite and 58-case held-out benchmark battery audit the unverified edges.",
            visual: .verificationPillars,
            microdetails: [
                "Kernel: 0 sorry, 0 @[extern], 0 native_decide, axioms [propext, Classical.choice, Quot.sound], 167+ Lean tests. In TCB outside kernel: compiler, GMP, parser, Float",
                "7-engine 187-case diff suite: FastLC 187/187, Web JS 187/187, HashMap 158/158 (0 bugs) vs Crowell JS 24 bugs despite 29/29 Test.js",
                "58-case 8-axis suite: geomean 1,508.5 -> 85.8 us (17.57x, 0 regressions, Peak RSS 45.0 MB), caught Axis-3 den != 1 (1,249 -> 106 us)"
            ],
            notes: SlideNotes(
                broadStroke: "Mirrors Theorem's fractional-proofs and bug-hunting posts: Crowell's 2009 JS passed 29/29 of its own tests yet had 24 differential bugs, 2024 Lean had 25, and our own adversarial audit caught 4 series and float bugs before shipping.",
                microdetails: [
                    "In the TCB (outside the Lean kernel): Lean compiler, C runtime and GMP, CLI parser, web and iPad UI, and truncated transcendental loops.",
                    "The 58-case suite stayed strictly held-out through climb-01..05, then caught the Axis-3 den != 1 gap that drove climb-07 from 1.07x to 11.8x with zero regressions."
                ],
                cutIfBehind: "Give just the three headline numbers: 0 sorry, 187/187 diff parity, and 17.57x across 58 cases.",
                expandIfAhead: "Name the unverified-layer bugs caught by the dual audit: (1+ε)^(1/ε) term-9 shift, divNewton garbage tail, and ratOfFloat saturation.",
                paceAnchor: "Start live demo on Slide 8 by 11:00."
            ),
            demoActions: [],
            qaItems: []
        ),

        // Slide 8 (index 7)
        InfSlide(
            id: 7,
            startTime: "11:00",
            gateTime: "13:00",
            gateSeconds: 780,
            title: "Live demo",
            thesis: "Tap any expression below to evaluate directly in compiled Lean 4.36, or draw live math with Apple Pencil.",
            visual: .liveDemoLauncher,
            microdetails: [
                "Every evaluation and plot point runs live in compiled Lean 4 FastLC over Tailscale",
                "Explore 1D curves, constant H ↦ N scaling curves, and 2D/3D heatmaps with Auto / Lin / SymLog Y / Log-Log",
                "Draw with Apple Pencil for Gemini Vision OCR (with silent Apple Vision fallback) straight into Lean 4"
            ],
            notes: SlideNotes(
                broadStroke: "Tap nonstd step, dstep(0), 1/x, x² + y², or write live math with Apple Pencil. In Split mode, every tap evaluates immediately in the adjacent Calculator pane.",
                microdetails: [
                    "Switch TV output between Slide and Calc if using an extended AirPlay or USB-C HDMI display.",
                    "If an audience member shouts a nasty expression like (1-ε²)/(1-ε) or H², type or write it live."
                ],
                cutIfBehind: "Run only nonstd step + one Apple Pencil drawing and close at 13:00.",
                expandIfAhead: "Show diff(1/(1+exp(-H·x)), x, 0, ε²) matching dstep(0), then 1/x and x² + y² heatmap.",
                paceAnchor: "Wrap cleanly by 13:00 (15:00 hard stop)."
            ),
            demoActions: [
                SlideDemoAction(title: "nonstd step", subtitle: "Lₕ(x) = 1/(1+exp(-H·x)) + 6 exact probes", expr: "1/(1+exp(-Hx))", clearForPencil: false),
                SlideDemoAction(title: "dstep(0)", subtitle: "Dirac peak (1/4)H - (1/48)ε + ...", expr: "dstep(0)", clearForPencil: false),
                SlideDemoAction(title: "diff(Lₕ, x, 0, ε²)", subtitle: "Central AD matches dstep(0) exact", expr: "diff(1/(1+exp(-Hx)), x, 0, eps^2)", clearForPencil: false),
                SlideDemoAction(title: "(1 - ε²) / (1 - ε)", subtitle: "Exact cancellation -> 1 + ε", expr: "(1-eps^2)/(1-eps)", clearForPencil: false),
                SlideDemoAction(title: "x² + y²", subtitle: "2D heatmap + exact Lean 4 probes", expr: "x^2 + y^2", clearForPencil: false),
                SlideDemoAction(title: "Draw with Apple Pencil", subtitle: "Clear canvas for live OCR -> Lean 4", expr: nil, clearForPencil: true)
            ],
            qaItems: [
                QACheatItem(
                    question: "What is in the TCB?",
                    answer: "In the TCB (outside the Lean kernel): Lean 4 compiler, C runtime and GMP, CLI parser, web/iPad UI, and truncated transcendental loops. Kernel proofs cover canonical FastLC ops, WF, 5 @[csimp] lemmas, CommRing/OrderedRing, and 24 FloatProofs theorems."
                ),
                QACheatItem(
                    question: "Why OrderedRing instead of Field?",
                    answer: "Finite-support sums ℚ[H^ℚ] form a computable ordered subring inside the Levi-Civita field. (1+ε)⁻¹ has infinite support, so invNewton truncates to a chosen order. We prove the algebraic quadratic step (newton_order_doubles) and array step kernel, not yet an end-to-end x * invNewton x n = 1 + O(εⁿ) theorem."
                ),
                QACheatItem(
                    question: "What does FloatProofs actually certify?",
                    answer: "diracCenter_at_100_certified certifies FloatLib Binary64 Sum2 on the 3-term dstep(0) constant (distinct from runtime Float.pow in FastLC.evalFinite), plus < 4 u64 overflow-free sigmoidB64, native-Float roundoff mixed bounds on s(1-s) and s(1-s)(1-2s), and N = 2^60 cancellation separation."
                ),
                QACheatItem(
                    question: "How much was AI-assisted vs owned?",
                    answer: "I set the mathematical specs, invariant boundaries, benchmark axes, and audit criteria. Agents accelerated Lean boilerplate, Kronecker proof grinding, and iPad scaffolding, while dual independent audits caught unverified-layer bugs that we fixed and regression-tested."
                )
            ]
        )
    ]
}
