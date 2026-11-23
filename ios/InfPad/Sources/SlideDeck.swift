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

/// 8 top-down broad-stroke + sharp-microdetail slides in Alok's voice
/// (strictly zero em/en dashes, zero exclamation marks, zero semicolons, zero meta-words).
enum SlideDeck {
    static let targetSeconds: Int = 13 * 60 // 13:00 target, 15:00 hard stop

    static let slides: [InfSlide] = [
        // Slide 1 (index 0)
        InfSlide(
            id: 0,
            startTime: "0:00",
            gateTime: "0:30",
            gateSeconds: 30,
            title: "Inf: Computable Infinitesimals in Lean 4",
            thesis: "One verified infinite unit H with eps = 1/H lets Lean compute calculus, step functions, and Dirac deltas algebraically.",
            visual: .titleHero,
            microdetails: [
                "Core ring Q[H^Q] proved in zero-Mathlib Lean 4.36 with zero sorry",
                "Dense 512-term multiplication runs in 0.38 ms instead of 112.6 ms",
                "187/187 differential parity against exact rational oracle across 7 engines"
            ],
            notes: SlideNotes(
                broadStroke: "Open fast on the goal: make infinitesimals and infinities computable, fast, and kernel-checked in Lean 4 so continuous math looks discrete.",
                microdetails: [
                    "Define H as a formal infinite unit and eps = 1/H as an infinitesimal.",
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
            thesis: "Split [a, b] into H pieces of width eps = 1/H. Integrals become finite-looking sums and ODEs become H-step loops.",
            visual: .continuumCut,
            microdetails: [
                "Distributions work linearly, yet products like delta^2 break down",
                "Dual numbers enforce eps^2 = 0, so you cannot invert eps or take H = 1/eps",
                "Full hyperreals *R need a non-principal ultrafilter, so Lean proves the computable ordered subring Q[H^Q] with division truncated to order"
            ],
            notes: SlideNotes(
                broadStroke: "Most proof engineering stays discrete because PL folks dislike floats and continuous math hides behind limits and distributions. Enlarging the number system turns continuous objects back into algebra.",
                microdetails: [
                    "Dual numbers are great for forward AD, yet eps^2 = 0 kills 1/eps and infinite heights.",
                    "Q[H^Q] is a computable ordered subring inside the Levi-Civita field, not a field, because 1/(1+eps) has infinite support and truncates to a chosen order."
                ],
                cutIfBehind: "Mention only dual numbers vs Q[H^Q] and skip the ultrafilter remark.",
                expandIfAhead: "Draw [a, b] ticks with Apple Pencil to show H subintervals of width eps.",
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
            thesis: "Plug H into a smooth logistic L_H(x) = 1/(1 + exp(-Hx)). Calc 1 turns it into a Dirac delta of height H/4, width eps, and area 1.",
            visual: .stepToDirac,
            microdetails: [
                "Exact symbolic derivative gives L_H'(0) = H/4 with zero distribution theory",
                "Central difference must step by eta = eps^2 because step eps jumps the cliff since H * eps = 1",
                "Pure AD prints dstep(0) = (1/4)H - (1/48)eps + (1/480)eps^3 ..., where -(1/48)eps is the O(eps^2) discretization tail"
            ],
            notes: SlideNotes(
                broadStroke: "Take 1/(1+exp(-Hx)). Macroscopically it looks like a Heaviside step, yet microscopically on +-8*eps it is smooth and differentiable by ordinary algebra.",
                microdetails: [
                    "Be explicit before anyone asks: exact L_H'(0) = H/4, while central difference at step eps^2 outputs (1/4)H - (1/48)eps + ... from the O(eps^2) difference quotient.",
                    "Tap the live jump button if you want a quick 15-second flash of the curve right now, or save the full demo for Slide 8."
                ],
                cutIfBehind: "Skip tapping live preview here and save all live calculator taps for Slide 8.",
                expandIfAhead: "Tap Live 1/(1+exp(-Hx)), toggle Micro +-8eps, and scrub N from 10 to 1000.",
                paceAnchor: "Leave Slide 3 by 4:00."
            ),
            demoActions: [
                SlideDemoAction(
                    title: "Live 1/(1+exp(-Hx))",
                    subtitle: "Open live step plot in Lean 4",
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
            title: "First tries by hand (2022-2024)",
            thesis: "Three hand-written prototypes across Julia, Python, and Lean 4 hit the same wall: unordered maps hide bugs and blow up runtime.",
            visual: .firstTriesTimeline,
            microdetails: [
                "2022 Julia Dict stalled at # TODO: convolution and # TODO: property based testing",
                "2024 Python alok/inf (Crowell JS fork) and infnum added Hypothesis PBT, yet stayed unverified",
                "Jul 2024 Lean HashMap left -- TODO use RbMap instead bc sorted? and shipped silent BEq (H == H^2) and ascending-sort signum (H - eps < 0) bugs"
            ],
            notes: SlideNotes(
                broadStroke: "Before proving anything fast, I tried writing this by hand three times across three languages. Every unordered map version failed in the exact same way.",
                microdetails: [
                    "In the July 2024 Lean HashMap version, even signum had to sort keys first, and it sorted ascending so H - eps read as negative.",
                    "BEq compared only matching keys, silently treating H == H^2 as equal."
                ],
                cutIfBehind: "Name only the July 2024 HashMap TODO comment and the ascending-sort signum bug.",
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
            title: "FastLC and verified speedups",
            thesis: "Replace HashMap with a canonical descending sorted array and prove a fast compute path equal to the spec via 5 literal @[csimp] rules.",
            visual: .speedupBars,
            microdetails: [
                "FastLC pairs descending sorted terms with an erased WF : Prop invariant checked against coeffOf",
                "Multiplication uses an untrusted grid guess plus a linear verified checker, then Array Int Karatsuba/Kronecker on GMP",
                "5 literal @[csimp] lemmas swap slow verified loops for fast kernels in C IR, with 5 rejected dead-end climbs logged"
            ],
            notes: SlideNotes(
                broadStroke: "Once the invariant lives in the type, signum is O(1) at index 0 and multiplication drops from 112.6 ms to 0.38 ms while staying provably equal to the naive spec.",
                microdetails: [
                    "Live cached bench table shows 296x dense mul (324x isolated), 425x inv (361x isolated), 13.9x sparse mul, and 636x signum.",
                    "Kronecker packing turns polynomial multiplication over rationals into one GMP big-integer multiply after verifying the uniform exponent grid."
                ],
                cutIfBehind: "Focus only on mul_dense (112.6 ms -> 0.38 ms) and the grid-guess + checker trick.",
                expandIfAhead: "Explain why 5 candidate optimizations were rejected when they regressed sparse cases or failed proofs.",
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
            title: "Lean 4.36 grind and FloatLib",
            thesis: "Keep the algebraic core zero-Mathlib using Lean 4.36 grind, and isolate IEEE-754 floating-point proofs in a nested FloatLib workspace.",
            visual: .grindAndFloatLib,
            microdetails: [
                "Core exports Lean.Grind CommRing and OrderedRing (truthfully not Field) with 23 GrindShowcase theorems and 32 by grind proofs",
                "Nested float-proofs/ builds 24 zero-sorry IEEE-754 theorems over FloatLib Binary64 without bloating core build times",
                "Certifies 24.99979 < v < 24.99980 on a verified Binary64 Sum2 model of 3-term dstep(0) at N=100, < 4 u64 sigmoidB64, and N = 2^60 cancellation separation"
            ],
            notes: SlideNotes(
                broadStroke: "Two clean boundaries: zero-Mathlib core for fast builds and grind ergonomics, plus a separate float-proofs workspace for IEEE-754 bounds.",
                microdetails: [
                    "Be precise for Rajashree: diracCenter_at_100_certified proves Binary64 Sum2 on the 3-term dstep(0) constant, separate from runtime Float.pow in FastLC.evalFinite.",
                    "At N = 2^60, FastLC keeps (H+1)^2 - H^2 - 2H - 1 = 0 exact (and (H+1)^2 - H^2 - 2H = 1, or (H+1)^2 - H^2 = 2H+1) while naive Float cancels completely to 0."
                ],
                cutIfBehind: "Mention only the zero-Mathlib grind core and the 24 FloatLib theorems.",
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
                "Kernel: 0 sorry, 0 @[extern], 0 native_decide, axioms strictly [propext, Classical.choice, Quot.sound], 167/167 Lean tests. In TCB outside kernel: compiler, GMP, parser, Float",
                "7-engine 187-case diff suite: FastLC 187/187, Web JS 187/187, HashMap 158/158 (0 bugs) vs Crowell JS 24 bugs (despite 29/29 Test.js), 2024 Lean 25, 2024 Python 31",
                "58-case 8-axis suite: geomean 1,508.5 -> 85.8 us (17.57x, 0 regressions, Peak RSS 45.0 MB), caught Axis-3 den != 1 (1,249 -> 106 us) and lean.h:1570 2^31 - 1 GMP cliff"
            ],
            notes: SlideNotes(
                broadStroke: "Be totally upfront about what is proved versus what sits in the TCB. Dual independent audits caught real unverified-layer series and float edge cases, and we fixed them all before today.",
                microdetails: [
                    "In the TCB (outside the Lean kernel): Lean compiler, C runtime and GMP, CLI parser, web and iPad UI, and truncated transcendental loops.",
                    "The 58-case suite stayed strictly held-out through climb-01..05, then caught the Axis-3 den != 1 gap that drove climb-07 from 1.07x to 11.8x with zero regressions."
                ],
                cutIfBehind: "Give just the three headline numbers: 0 sorry, 187/187 diff parity, and 17.57x across 58 cases.",
                expandIfAhead: "Mention the 3 unverified-layer bugs caught by the dual audit: (1+eps)^(1/eps) term-9 shift, divNewton garbage tail, and ratOfFloat saturation.",
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
            thesis: "Tap any expression below to jump straight into compiled Lean 4.36, or draw live math with Apple Pencil.",
            visual: .liveDemoLauncher,
            microdetails: [
                "Every evaluation runs live in compiled Lean 4 FastLC over Tailscale",
                "Watch 1/(1+exp(-Hx)) tighten into a step function as H -> N scrubs from 10 to 1000",
                "Draw with Apple Pencil for Gemini Vision OCR (with silent Apple Vision fallback) straight into Lean 4"
            ],
            notes: SlideNotes(
                broadStroke: "Launch 1/(1+exp(-Hx)), drag N from 10 to 1000, toggle Micro +-8eps, then run dstep(0) and draw an expression with Apple Pencil.",
                microdetails: [
                    "Use the <- Slides button in Calculator anytime to jump back to Q&A.",
                    "If an audience member shouts a nasty expression like (1-eps^2)/(1-eps) or 1/x, type or write it live."
                ],
                cutIfBehind: "Run only 1/(1+exp(-Hx)) + one Apple Pencil drawing and close at 13:00.",
                expandIfAhead: "Show diff(1/(1+exp(-Hx)), x, 0, eps^2) matching dstep(0), then 1/x showing -H, undef, H^2, H.",
                paceAnchor: "Wrap cleanly by 13:00 (15:00 hard stop)."
            ),
            demoActions: [
                SlideDemoAction(title: "1/(1+exp(-Hx))", subtitle: "Step curve + 6 exact probes", expr: "1/(1+exp(-Hx))", clearForPencil: false),
                SlideDemoAction(title: "dstep(0)", subtitle: "Dirac peak (1/4)H - (1/48)eps...", expr: "dstep(0)", clearForPencil: false),
                SlideDemoAction(title: "diff(..., eps^2)", subtitle: "Central AD matches dstep(0)", expr: "diff(1/(1+exp(-Hx)), x, 0, eps^2)", clearForPencil: false),
                SlideDemoAction(title: "(1-eps^2)/(1-eps)", subtitle: "Exact cancellation -> 1 + eps", expr: "(1-eps^2)/(1-eps)", clearForPencil: false),
                SlideDemoAction(title: "1/x", subtitle: "Pole plot + exact -H, H^2, H", expr: "1/x", clearForPencil: false),
                SlideDemoAction(title: "Draw with Apple Pencil", subtitle: "Clear canvas for live OCR -> Lean 4", expr: nil, clearForPencil: true)
            ],
            qaItems: [
                QACheatItem(
                    question: "What is in the TCB?",
                    answer: "In the TCB (outside the Lean kernel): Lean 4 compiler, C runtime and GMP, CLI parser, web/iPad UI, and truncated transcendental loops. Kernel proofs cover canonical FastLC ops, WF, 5 @[csimp] lemmas, CommRing/OrderedRing, and 24 FloatProofs theorems."
                ),
                QACheatItem(
                    question: "Why OrderedRing instead of Field?",
                    answer: "Finite-support sums Q[H^Q] form a computable ordered subring inside the Levi-Civita field. 1/(1+eps) has infinite support, so invNewton truncates to a chosen order. We prove the algebraic quadratic step (newton_order_doubles) and array step kernel, not yet an end-to-end x * invNewton x n = 1 + O(eps^n) theorem."
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
