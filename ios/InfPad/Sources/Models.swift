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
}

struct FnPlot: Codable, Equatable {
    let varName: String?
    let x_min: Double
    let x_max: Double
    let y_min: Double
    let y_max: Double
    let points: [[Double]]
    let zoom_x_min: Double?
    let zoom_x_max: Double?
    let zoom_y_min: Double?
    let zoom_y_max: Double?
    let zoom_points: [[Double]]?

    enum CodingKeys: String, CodingKey {
        case varName = "var"
        case x_min, x_max, y_min, y_max, points
        case zoom_x_min, zoom_x_max, zoom_y_min, zoom_y_max, zoom_points
    }

    var hasZoom: Bool {
        if let zp = zoom_points, !zp.isEmpty { return true }
        return false
    }
}

struct EvalResponse: Codable, Equatable {
    let ok: Bool
    let kind: String?
    let varName: String?
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
    let engine: String?
    let serverMs: Double?
    let error: String?

    enum CodingKeys: String, CodingKey {
        case ok, kind
        case varName = "var"
        case input, exact, approx, value, regime, sign, dominant, std_part
        case term_count, eval_N, eval_finite, terms, probes, plot, engine, serverMs, error
    }

    var isFunction: Bool {
        kind == "fn" && plot != nil
    }

    /// Instant local preview of substituting H ↦ N from the exact terms array (used while scrubbing slider).
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
    static let defaultServerURL = "https://mac.tailbf1ac1.ts.net/inf-api"
    static let simulatorLocalURL = "http://127.0.0.1:4420"

    static let starterChips: [StarterChip] = [
        StarterChip(label: "1/(1+exp(-Hx))", expr: "1/(1+exp(-Hx))", hint: "Logistic step function"),
        StarterChip(label: "dstep(x)", expr: "dstep(x)", hint: "Dirac delta curve"),
        StarterChip(label: "dstep(0)", expr: "dstep(0)", hint: "Dirac delta peak"),
        StarterChip(label: "ddstep(eps)", expr: "ddstep(eps)", hint: "Delta derivative"),
        StarterChip(label: "exp(H*eps)", expr: "exp(H*eps)", hint: "Exact cancellation"),
        StarterChip(label: "(1 + eps)^(-1)", expr: "(1 + eps)^(-1)", hint: "Geometric series"),
        StarterChip(label: "diff(x^4, x, 2)", expr: "diff(x^4, x, 2)", hint: "Infinitesimal slope"),
    ]

    static let quickSymbols: [String] = [
        "H", "eps", "x", "^", "/", "(", ")", "+", "-", "*", "exp(", "dstep(", "ddstep(", "std("
    ]
}
