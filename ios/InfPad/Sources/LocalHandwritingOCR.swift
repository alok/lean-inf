import Foundation
import UIKit
import Vision

/// On-device Apple Vision Neural Engine handwriting-to-text OCR + deterministic lean-inf sanitizer.
/// Used ONLY as a silent fallback when remote Gemini OCR is unavailable; the recognized expression
/// is ALWAYS evaluated by the real Lean 4 `FastLC` server (`GET /eval`).
enum LocalHandwritingOCR {
    struct Recognition {
        let rawExpr: String
        let normalizedExpr: String
        let confidence: Double
        let ocrMs: Double
    }

    private static let mathVocab: [String] = [
        "dstep", "ddstep", "step", "exp", "eps", "diff", "deriv",
        "std", "sin", "cos", "tan", "ln", "log", "sqrt", "abs",
        "Hx", "H*x", "1/(1+exp(-Hx))", "dstep(0)", "dstep(x)", "ddstep(eps)"
    ]

    private static let superscriptMap: [Character: String] = [
        "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4",
        "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9",
        "⁺": "+", "⁻": "-", "⁽": "(", "⁾": ")"
    ]

    static func recognize(pngData: Data) async -> Recognition {
        let t0 = CFAbsoluteTimeGetCurrent()
        let (rawText, confidence) = await Task.detached(priority: .userInitiated) {
            Self.runVisionOCR(pngData: pngData)
        }.value
        let ocrMs = ((CFAbsoluteTimeGetCurrent() - t0) * 1000.0 * 100.0).rounded() / 100.0
        let normalized = sanitize(rawText)
        return Recognition(
            rawExpr: rawText,
            normalizedExpr: normalized,
            confidence: confidence,
            ocrMs: ocrMs
        )
    }

    private static func runVisionOCR(pngData: Data) -> (String, Double) {
        guard let image = UIImage(data: pngData), let cgImage = image.cgImage else {
            return ("", 0.0)
        }

        let request = VNRecognizeTextRequest()
        request.recognitionLevel = .accurate
        request.usesLanguageCorrection = false
        request.recognitionLanguages = ["en-US"]
        request.customWords = mathVocab

        let handler = VNImageRequestHandler(cgImage: cgImage, options: [:])
        do {
            try handler.perform([request])
        } catch {
            return ("", 0.0)
        }

        guard let observations = request.results, !observations.isEmpty else {
            return ("", 0.0)
        }

        struct BoxText {
            let text: String
            let box: CGRect
            let conf: Double
        }
        let items: [BoxText] = observations.compactMap { obs in
            guard let top = obs.topCandidates(1).first else { return nil }
            let t = top.string.trimmingCharacters(in: .whitespacesAndNewlines)
            guard !t.isEmpty else { return nil }
            return BoxText(text: t, box: obs.boundingBox, conf: Double(top.confidence))
        }
        guard !items.isEmpty else { return ("", 0.0) }

        let avgConf = items.reduce(0.0) { $0 + $1.conf } / Double(items.count)

        // Stacked 2-row fraction detection (numerator directly above denominator)
        if items.count == 2 {
            let a = items[0], b = items[1]
            let xOverlap = min(a.box.maxX, b.box.maxX) - max(a.box.minX, b.box.minX)
            let minW = min(a.box.width, b.box.width)
            let yGap = abs(a.box.midY - b.box.midY)
            if minW > 0 && xOverlap / minW > 0.35 && yGap > max(a.box.height, b.box.height) * 0.65 {
                let topItem = a.box.midY > b.box.midY ? a : b
                let botItem = a.box.midY > b.box.midY ? b : a
                return ("(\(topItem.text))/(\(botItem.text))", avgConf)
            }
        }

        let sorted = items.sorted { $0.box.minX < $1.box.minX }
        var combined = sorted[0].text
        var prev = sorted[0]
        for cur in sorted.dropFirst() {
            let isRaisedSuperscript = cur.box.midY > prev.box.midY + prev.box.height * 0.32 && cur.box.height < prev.box.height * 0.8
            if isRaisedSuperscript && !cur.text.hasPrefix("^") {
                combined += "^(\(cur.text))"
            } else {
                combined += " " + cur.text
            }
            prev = cur
        }
        return (combined, avgConf)
    }

    static func sanitize(_ raw: String) -> String {
        var s = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !s.isEmpty else { return "" }

        s = s.replacingOccurrences(of: "`", with: "")
            .replacingOccurrences(of: "$", with: "")

        s = regexReplace(s, pattern: "([A-Za-z])([εϵɛ])", template: "$1*eps")
        s = regexReplace(s, pattern: "([εϵɛ])([A-Za-z])", template: "eps*$2")

        let directMap: [(String, String)] = [
            ("−", "-"), ("–", "-"), ("—", "-"), ("‒", "-"),
            ("×", "*"), ("·", "*"), ("⋅", "*"), ("∙", "*"),
            ("÷", "/"), ("⁄", "/"), ("∕", "/"),
            ("≤", "<="), ("≥", ">="), ("≠", "!="),
            ("∞", "H"), ("ω", "H"),
            ("ε", "eps"), ("ϵ", "eps"), ("ɛ", "eps"),
            ("π", "pi"),
            ("（", "("), ("）", ")"), ("［", "["), ("］", "]"),
        ]
        for (from, to) in directMap {
            s = s.replacingOccurrences(of: from, with: to)
        }

        s = regexReplace(s, pattern: "\\bdstep\\s*\\(\\s*[Oo]\\s*\\)", template: "dstep(0)")
        s = regexReplace(s, pattern: "\\bstep\\s*\\(\\s*[Oo]\\s*\\)", template: "step(0)")
        s = regexReplace(s, pattern: "\\bexp\\s*\\(\\s*-\\s*H\\s*x\\s*\\)", template: "exp(-H*x)")

        s = regexReplace(s, pattern: "√\\s*\\(([^()]+)\\)", template: "sqrt($1)")
        s = regexReplace(s, pattern: "√\\s*([A-Za-z0-9_.]+)", template: "sqrt($1)")

        s = replaceSuperscripts(s)
        s = rewriteEToExp(s)

        let glued: [(String, String)] = [
            ("\\bHeps\\b", "H*eps"),
            ("\\bepsH\\b", "eps*H"),
            ("\\bHx\\b", "H*x"),
            ("\\bxH\\b", "x*H"),
            ("\\bhx\\b", "h*x"),
            ("\\bxeps\\b", "x*eps"),
            ("\\bepsx\\b", "eps*x"),
        ]
        for (pat, rep) in glued {
            s = regexReplace(s, pattern: pat, template: rep)
        }

        return regexReplace(s, pattern: "\\s+", template: " ").trimmingCharacters(in: .whitespacesAndNewlines)
    }

    private static func replaceSuperscripts(_ input: String) -> String {
        var out = ""
        var run = ""
        func flushRun() {
            guard !run.isEmpty else { return }
            if run.hasPrefix("(") && run.hasSuffix(")") {
                out += "^\(run)"
            } else if run.contains("-") || run.contains("+") {
                out += "^(\(run))"
            } else {
                out += "^\(run)"
            }
            run = ""
        }
        for ch in input {
            if let mapped = superscriptMap[ch] {
                run += mapped
            } else {
                flushRun()
                out.append(ch)
            }
        }
        flushRun()
        return out
    }

    private static func rewriteEToExp(_ input: String) -> String {
        let chars = Array(input)
        var out = ""
        var i = 0
        while i < chars.count {
            let wordBefore = (i == 0) || !(chars[i - 1].isLetter || chars[i - 1].isNumber || chars[i - 1] == "_")
            if chars[i] == "e" && wordBefore {
                var j = i + 1
                while j < chars.count && chars[j] == " " { j += 1 }
                if j < chars.count && chars[j] == "^" {
                    j += 1
                    while j < chars.count && chars[j] == " " { j += 1 }
                    var signPrefix = ""
                    if j + 1 < chars.count && (chars[j] == "-" || chars[j] == "+") && chars[j + 1] == "(" {
                        signPrefix = String(chars[j])
                        j += 1
                    }
                    if j < chars.count && chars[j] == "(" {
                        var depth = 1
                        var k = j + 1
                        while k < chars.count && depth > 0 {
                            if chars[k] == "(" { depth += 1 }
                            else if chars[k] == ")" { depth -= 1 }
                            k += 1
                        }
                        if depth == 0 {
                            let inner = rewriteEToExp(String(chars[(j + 1)..<(k - 1)]))
                            out += signPrefix.isEmpty ? "exp(\(inner))" : "exp(\(signPrefix)(\(inner)))"
                            i = k
                            continue
                        }
                    } else if j < chars.count {
                        var k = j
                        if chars[k] == "+" || chars[k] == "-" { k += 1 }
                        while k < chars.count {
                            let ch = chars[k]
                            if ch.isLetter || ch.isNumber || ch == "_" || ch == "." || ch == "*" || ch == "^" {
                                k += 1
                            } else {
                                break
                            }
                        }
                        if k > j {
                            let atom = String(chars[j..<k])
                            out += "exp(\(atom))"
                            i = k
                            continue
                        }
                    }
                }
            }
            out.append(chars[i])
            i += 1
        }
        return out
    }

    private static func regexReplace(_ input: String, pattern: String, template: String) -> String {
        guard let re = try? NSRegularExpression(pattern: pattern) else { return input }
        let range = NSRange(input.startIndex..., in: input)
        return re.stringByReplacingMatches(in: input, options: [], range: range, withTemplate: template)
    }
}
