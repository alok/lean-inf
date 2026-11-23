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

struct EvalResponse: Codable, Equatable {
    let ok: Bool
    let kind: String?
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
    let engine: String?
    let serverMs: Double?
    let error: String?

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
        // Split on " + " or " - " only outside parentheses
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
        StarterChip(label: "dstep(0)", expr: "dstep(0)", hint: "Dirac delta peak"),
        StarterChip(label: "ddstep(eps)", expr: "ddstep(eps)", hint: "Delta derivative"),
        StarterChip(label: "exp(H*eps)", expr: "exp(H*eps)", hint: "Exact cancellation"),
        StarterChip(label: "(1 + eps)^(-1)", expr: "(1 + eps)^(-1)", hint: "Geometric series"),
        StarterChip(label: "diff(x^4, x, 2)", expr: "diff(x^4, x, 2)", hint: "Infinitesimal slope"),
    ]

    static let quickSymbols: [String] = [
        "H", "eps", "^", "/", "(", ")", "+", "-", "*", "dstep(", "ddstep(", "exp(", "std("
    ]
}
