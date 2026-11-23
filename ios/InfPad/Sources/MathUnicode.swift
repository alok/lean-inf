import Foundation

/// Clean mathematical Unicode typography for iPad display labels (while keeping raw ASCII expressions for Lean 4 API).
enum MathUnicode {
    private static let subDigits: [Character: Character] = [
        "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄",
        "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉", "-": "₋"
    ]

    private static let superDigits: [Character: Character] = [
        "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
        "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "-": "⁻"
    ]

    static func subscriptInt(_ n: Int) -> String {
        String(String(n).map { subDigits[$0] ?? $0 })
    }

    static func superscriptInt(_ n: Int) -> String {
        String(String(n).map { superDigits[$0] ?? $0 })
    }

    static func powerOfTen(_ exponent: Int) -> String {
        "10\(superscriptInt(exponent))"
    }

    /// Formats `fₙ(arg)` with true Unicode subscripts (e.g. `f₁₀₀(0)` instead of `f_100(0)`).
    static func fnSubscript(_ n: Int, arg: String) -> String {
        "f\(subscriptInt(n))(\(arg))"
    }

    /// Formats a numeric value cleanly for plot axis ticks and HUD readouts.
    static func formatTick(_ val: Double) -> String {
        if !val.isFinite { return "—" }
        if abs(val) < 1e-9 { return "0" }
        let mag = abs(val)
        if mag >= 1000 || mag < 0.01 {
            let exp = Int(floor(log10(mag)))
            let mant = val / pow(10.0, Double(exp))
            if abs(abs(mant) - 1.0) < 0.05 {
                return (val < 0 ? "-" : "") + powerOfTen(exp)
            }
            return String(format: "%.1f×%@", mant, powerOfTen(exp))
        }
        if abs(val - val.rounded()) < 1e-4 {
            return String(format: "%.0f", val.rounded())
        }
        return String(format: "%.2g", val)
    }

    static func formatReadout(_ val: Double) -> String {
        if !val.isFinite { return "undef" }
        if abs(val) < 1e-9 { return "0" }
        let mag = abs(val)
        if mag >= 1e5 || mag < 1e-4 {
            let exp = Int(floor(log10(mag)))
            let mant = val / pow(10.0, Double(exp))
            return String(format: "%.3f×%@", mant, powerOfTen(exp))
        }
        return String(format: "%.4f", val)
    }
}
