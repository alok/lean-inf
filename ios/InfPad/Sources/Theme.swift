import SwiftUI
import UIKit

/// Astigmatism-friendly Warm Paper palette (default) + low-glare Soft Slate Dark option.
/// Avoids pure white on pure black to prevent halation and visual streaking on iPad Pro displays.
struct InfTheme {
    let isDark: Bool

    var paperBackground: Color {
        isDark
            ? Color(red: 0.110, green: 0.110, blue: 0.122)   // #1c1c1f
            : Color(red: 0.973, green: 0.969, blue: 0.949)   // #f8f7f2
    }

    var surfaceCard: Color {
        isDark
            ? Color(red: 0.149, green: 0.153, blue: 0.169)   // #26272b
            : Color(red: 0.941, green: 0.933, blue: 0.902)   // #f0eee6
    }

    var elevatedCard: Color {
        isDark
            ? Color(red: 0.184, green: 0.188, blue: 0.208)   // #2f3035
            : Color(red: 1.000, green: 0.996, blue: 0.984)   // #fffefb
    }

    var borderSubtle: Color {
        isDark
            ? Color.white.opacity(0.11)
            : Color(red: 0.067, green: 0.094, blue: 0.153).opacity(0.12)
    }

    var primaryInk: Color {
        isDark
            ? Color(red: 0.902, green: 0.894, blue: 0.863)   // #e6e4dc (never pure #ffffff)
            : Color(red: 0.067, green: 0.094, blue: 0.153)   // #111827
    }

    var secondaryInk: Color {
        isDark
            ? Color(red: 0.659, green: 0.667, blue: 0.706)   // #a8aab4
            : Color(red: 0.294, green: 0.333, blue: 0.388)   // #4b5563
    }

    var accentCobalt: Color {
        isDark
            ? Color(red: 0.376, green: 0.647, blue: 0.980)   // #60a5fa
            : Color(red: 0.114, green: 0.306, blue: 0.847)   // #1d4ed8
    }

    var canvasDotColor: Color {
        isDark
            ? Color.white.opacity(0.08)
            : Color(red: 0.067, green: 0.094, blue: 0.153).opacity(0.10)
    }

    var canvasInkUIColor: UIColor {
        isDark
            ? UIColor(red: 0.902, green: 0.894, blue: 0.863, alpha: 1.0)
            : UIColor(red: 0.067, green: 0.094, blue: 0.153, alpha: 1.0)
    }

    var successGreen: Color {
        isDark
            ? Color(red: 0.290, green: 0.871, blue: 0.502)
            : Color(red: 0.082, green: 0.502, blue: 0.239)
    }

    var errorRed: Color {
        isDark
            ? Color(red: 0.973, green: 0.443, blue: 0.443)
            : Color(red: 0.725, green: 0.110, blue: 0.110)
    }

    func regimeStyle(_ regime: String?) -> (fg: Color, bg: Color, label: String) {
        switch (regime ?? "").lowercased() {
        case "infinite":
            return isDark
                ? (Color(red: 0.992, green: 0.729, blue: 0.455), Color(red: 0.486, green: 0.176, blue: 0.071).opacity(0.45), "INFINITE")
                : (Color(red: 0.604, green: 0.204, blue: 0.071), Color(red: 1.000, green: 0.929, blue: 0.835), "INFINITE")
        case "infinitesimal":
            return isDark
                ? (Color(red: 0.769, green: 0.710, blue: 0.992), Color(red: 0.298, green: 0.114, blue: 0.584).opacity(0.45), "INFINITESIMAL")
                : (Color(red: 0.357, green: 0.129, blue: 0.714), Color(red: 0.929, green: 0.914, blue: 0.996), "INFINITESIMAL")
        case "finite":
            return isDark
                ? (Color(red: 0.576, green: 0.773, blue: 0.992), Color(red: 0.118, green: 0.251, blue: 0.686).opacity(0.45), "FINITE")
                : (Color(red: 0.118, green: 0.251, blue: 0.686), Color(red: 0.859, green: 0.918, blue: 0.996), "FINITE")
        case "zero":
            return (secondaryInk, surfaceCard, "ZERO")
        default:
            return (accentCobalt, accentCobalt.opacity(0.14), "RESULT")
        }
    }
}
