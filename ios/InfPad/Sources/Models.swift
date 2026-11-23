import Foundation

struct HealthResponse: Codable {
    let ok: Bool
    let engine: String?
    let lean: String?
    let ocrConfigured: Bool?
    let uptimeMs: Double?
    let pingMs: Double?
}

struct LCTerm: Codable, Identifiable, Equatable {
    let exp: String
    let exp_f: Double
    let coeff: String
    let coeff_f: Double

    var id: String { "\(exp):\(coeff)" }
}

struct FnProbe: Codable, Identifiable, Equatable {
    let x_label: String
    let ok: Bool
    let exact: String?
    let approx: String?
    let regime: String?
    let eval_finite: Double?
    let error: String?

    var id: String { x_label }

    enum CodingKeys: String, CodingKey {
        case x_label, label, ok, exact, approx, regime, eval_finite, error
    }

    init(
        x_label: String,
        ok: Bool,
        exact: String?,
        approx: String?,
        regime: String?,
        eval_finite: Double?,
        error: String?
    ) {
        self.x_label = x_label
        self.ok = ok
        self.exact = exact
        self.approx = approx
        self.regime = regime
        self.eval_finite = eval_finite
        self.error = error
    }

    init(from decoder: Decoder) throws {
        let c = try decoder.container(keyedBy: CodingKeys.self)
        let primaryLabel = try c.decodeIfPresent(String.self, forKey: .x_label)
        let altLabel = try c.decodeIfPresent(String.self, forKey: .label)
        self.x_label = primaryLabel ?? altLabel ?? "?"
        self.ok = try c.decodeIfPresent(Bool.self, forKey: .ok) ?? false
        self.exact = try c.decodeIfPresent(String.self, forKey: .exact)
        self.approx = try c.decodeIfPresent(String.self, forKey: .approx)
        self.regime = try c.decodeIfPresent(String.self, forKey: .regime)
        self.eval_finite = try c.decodeIfPresent(Double.self, forKey: .eval_finite)
        self.error = try c.decodeIfPresent(String.self, forKey: .error)
    }

    func encode(to encoder: Encoder) throws {
        var c = encoder.container(keyedBy: CodingKeys.self)
        try c.encode(x_label, forKey: .x_label)
        try c.encode(ok, forKey: .ok)
        try c.encodeIfPresent(exact, forKey: .exact)
        try c.encodeIfPresent(approx, forKey: .approx)
        try c.encodeIfPresent(regime, forKey: .regime)
        try c.encodeIfPresent(eval_finite, forKey: .eval_finite)
        try c.encodeIfPresent(error, forKey: .error)
    }
}

struct FnPlot: Codable, Equatable {
    let varName: String?
    let vars: [String]?
    let x_min: Double?
    let x_max: Double?
    let y_min: Double?
    let y_max: Double?
    let points: [[Double]]?
    let zoom_x_min: Double?
    let zoom_x_max: Double?
    let zoom_y_min: Double?
    let zoom_y_max: Double?
    let zoom_points: [[Double]]?
    // Generic finite-projection constant plot fields
    let finite_y: Double?
    let scale_curve: [[Double]]?
    let scale_hint: String?
    // 2-var (fn2) & 3-var (fn3) heatmap fields (supported nested inside `plot` or top-level)
    let grid_size: Int?
    let values: [Double?]?
    let slice_values: [Double]?
    let slices: [[Double?]]?
    let z_min: Double?
    let z_max: Double?

    enum CodingKeys: String, CodingKey {
        case varName = "var"
        case vars
        case x_min, x_max, y_min, y_max, points
        case zoom_x_min, zoom_x_max, zoom_y_min, zoom_y_max, zoom_points
        case finite_y, scale_curve, scale_hint
        case grid_size, values, slice_values, slices, z_min, z_max
    }

    var hasZoom: Bool {
        if let zp = zoom_points, !zp.isEmpty { return true }
        return false
    }

    var hasMacroPoints: Bool {
        if let p = points, p.count >= 2 { return true }
        return false
    }

    var hasScaleCurve: Bool {
        if let sc = scale_curve, sc.count >= 2 { return true }
        return false
    }
}

struct EvalResponse: Codable, Equatable {
    let ok: Bool
    let kind: String?
    let varName: String?
    let vars: [String]?
    let input: String?
    let exact: String?
    let approx: String?
    let value: Bool?
    let regime: String?
    let sign: Int?
    let dominant: String?
    let std_part: String?
    let term_count: Int?
    let eval_N: Double?
    let eval_finite: Double?
    let terms: [LCTerm]?
    let probes: [FnProbe]?
    let plot: FnPlot?
    let plot_decision: String?
    let plot_reason: String?
    let scale_hint: String?
    // Optional top-level fn2/fn3 grid fields (backwards-compatible with both top-level and nested `plot`)
    let grid_size: Int?
    let x_min: Double?
    let x_max: Double?
    let y_min: Double?
    let y_max: Double?
    let z_min: Double?
    let z_max: Double?
    let values: [Double?]?
    let slice_values: [Double]?
    let slices: [[Double?]]?
    let engine: String?
    let serverMs: Double?
    let error: String?

    enum CodingKeys: String, CodingKey {
        case ok, kind
        case varName = "var"
        case vars
        case input, exact, approx, value, regime, sign, dominant, std_part
        case term_count, eval_N, eval_finite, terms, probes, plot
        case plot_decision, plot_reason, scale_hint
        case grid_size, x_min, x_max, y_min, y_max, z_min, z_max
        case values, slice_values, slices
        case engine, serverMs, error
    }

    var isFunction: Bool {
        kind == "fn" && (plot?.hasMacroPoints ?? false)
    }

    var isHeatmap: Bool {
        guard kind == "fn2" || kind == "fn3" else { return false }
        return effectiveGridSize > 0 && (effectiveValues != nil || !(effectiveSlices?.isEmpty ?? true))
    }

    var isFiniteProjectionPlot: Bool {
        kind == "num" && plot_decision == "finite_projection" && (plot?.hasScaleCurve ?? false)
    }

    var isSkippedNonFinitePlot: Bool {
        plot_decision == "skip_nonfinite"
    }

    var effectiveScaleHint: String? {
        scale_hint ?? plot?.scale_hint
    }

    var effectiveVarName: String {
        plot?.varName ?? varName ?? "x"
    }

    var effectiveVars: [String] {
        plot?.vars ?? vars ?? ["x", "y"]
    }

    var effectiveGridSize: Int {
        plot?.grid_size ?? grid_size ?? 0
    }

    var effectiveValues: [Double?]? {
        plot?.values ?? values
    }

    var effectiveSliceValues: [Double]? {
        plot?.slice_values ?? slice_values
    }

    var effectiveSlices: [[Double?]]? {
        plot?.slices ?? slices
    }

    var effectiveZRange: (min: Double, max: Double) {
        let lo = plot?.z_min ?? z_min ?? -1.0
        let hi = plot?.z_max ?? z_max ?? 1.0
        return (lo, hi)
    }

    var effectiveAxisRanges: (xMin: Double, xMax: Double, yMin: Double, yMax: Double) {
        (
            plot?.x_min ?? x_min ?? -1.0,
            plot?.x_max ?? x_max ?? 1.0,
            plot?.y_min ?? y_min ?? -1.0,
            plot?.y_max ?? y_max ?? 1.0
        )
    }

    /// Instant local preview of substituting H ↦ N from the exact terms array returned by Lean 4 while dragging slider.
    func localEvalFinite(at bigN: Double) -> Double? {
        guard kind == "num", let terms, !terms.isEmpty else {
            return eval_finite
        }
        var sum = 0.0
        for term in terms {
            let termVal = term.coeff_f * pow(bigN, term.exp_f)
            if termVal.isNaN || termVal.isInfinite {
                return nil
            }
            sum += termVal
            if sum.isNaN || sum.isInfinite {
                return nil
            }
        }
        return sum
    }

    /// Formats the leading terms cleanly while allowing full rational tails to be collapsed/expanded.
    func splitExactPreview(maxVisibleTerms: Int = 3) -> (head: String, tailCount: Int) {
        guard let exact else { return ("", 0) }
        guard let terms, terms.count > maxVisibleTerms else {
            return (exact, 0)
        }
        var parts: [String] = []
        var current = ""
        var depth = 0
        let chars = Array(exact)
        var i = 0
        while i < chars.count {
            let ch = chars[i]
            if ch == "(" { depth += 1 }
            else if ch == ")" { depth = max(0, depth - 1) }

            if depth == 0 && i + 2 < chars.count && ch == " " && (chars[i + 1] == "+" || chars[i + 1] == "-") && chars[i + 2] == " " {
                parts.append(current)
                current = (chars[i + 1] == "+" ? "+ " : "− ")
                i += 3
                continue
            }
            current.append(ch)
            i += 1
        }
        if !current.isEmpty {
            parts.append(current)
        }
        guard parts.count > maxVisibleTerms else {
            return (exact, 0)
        }
        let head = parts.prefix(maxVisibleTerms).joined(separator: " ")
        return (head, parts.count - maxVisibleTerms)
    }
}

struct OcrMetadata: Codable, Equatable {
    let expr: String?
    let rawExpr: String?
    let confidence: Double?
    let note: String?
    let model: String?
    let ocrMs: Double?
}

struct OcrEvalResponse: Codable {
    let ok: Bool
    let error: String?
    let recognizedExpr: String?
    let normalizedExpr: String?
    let confidence: Double?
    let note: String?
    let model: String?
    let ocrMs: Double?
    let serverMs: Double?
    let ocr: OcrMetadata?
    let eval: EvalResponse?
}

struct HistoryEntry: Codable, Identifiable, Equatable {
    let id: UUID
    let timestamp: Date
    let expression: String
    let recognizedExpr: String?
    let exactSummary: String
    let regime: String?
    let ocrMs: Double?
    let leanMs: Double?
    let hasDrawing: Bool
    let evalSnapshot: EvalResponse?
}

struct StarterChip: Identifiable {
    let id = UUID()
    let label: String
    let expr: String
    let hint: String
}

enum InfPadPresets {
    static let defaultServerURL = "https://epicycle-2.tailbf1ac1.ts.net/inf-api"
    static let legacyServerURL = "https://mac.tailbf1ac1.ts.net/inf-api"
    static let simulatorLocalURL = "http://127.0.0.1:4420"

    static let starterChips: [StarterChip] = [
        StarterChip(
            label: "nonstd step",
            expr: "1/(1+exp(-Hx))",
            hint: "Nonstandard logistic step Lₕ(x) = 1/(1 + exp(-Hx)): 0 for x < 0, 1/2 at 0, 1 for x > 0"
        ),
        StarterChip(
            label: "dstep(x)",
            expr: "dstep(x)",
            hint: "Central difference quotient (Lₕ(x + ε²) - Lₕ(x - ε²)) / (2ε²) of the step function: a Dirac delta of height H/4, width O(ε), area 1 (no hand-coded derivative rule)"
        ),
        StarterChip(
            label: "dstep(0)",
            expr: "dstep(0)",
            hint: "Dirac delta peak at x = 0 via central difference at step ε²: (1/4)H - (1/48)ε + (1/480)ε³ - ... (~25 at H ↦ 100)"
        ),
        StarterChip(
            label: "ddstep(ε)",
            expr: "ddstep(eps)",
            hint: "Second central difference (Lₕ(x + ε²) - 2·Lₕ(x) + Lₕ(x - ε²)) / ε⁴ of the step function (Dirac dipole)"
        ),
        StarterChip(
            label: "1/x",
            expr: "1/x",
            hint: "Reciprocal pole at x = 0: f(-ε) = -H, f(0) undef, f(ε²) = H², f(ε) = H"
        ),
        StarterChip(
            label: "exp(H·ε)",
            expr: "exp(H*eps)",
            hint: "Exact cancellation: H·ε = 1, so exp(H·ε) = e"
        ),
        StarterChip(
            label: "(1 + ε)⁻¹",
            expr: "(1 + eps)^(-1)",
            hint: "Geometric series 1 - ε + ε² - ε³ + ... via Newton inversion"
        ),
        StarterChip(
            label: "diff(x⁴, x, 2)",
            expr: "diff(x^4, x, 2)",
            hint: "Automatic derivative (f(2 + ε) - f(2)) / ε = 32 + 24ε + 8ε² + ε³"
        ),
        StarterChip(
            label: "x² + y²",
            expr: "x^2 + y^2",
            hint: "Two-variable paraboloid heatmap in (x, y) with exact Lean 4 probes"
        ),
    ]

    static let quickSymbols: [String] = [
        "H", "eps", "x", "y", "z", "^", "/", "(", ")", "+", "-", "*", "exp(", "dstep(", "ddstep(", "std("
    ]
}
