import Foundation
import Observation
import PencilKit
import SwiftUI

enum InfPadTab: String, CaseIterable, Identifiable {
    case calculator = "Calculator"
    case split = "Split"
    case slides = "Slides"

    var id: String { rawValue }
}

enum ExternalOutputMode: String, CaseIterable, Identifiable {
    case slide = "Slide"
    case calculator = "Calc"

    var id: String { rawValue }
}

@MainActor
@Observable
final class InfPadStore {
    var serverURL: String {
        didSet { UserDefaults.standard.set(serverURL, forKey: "infpad.serverURL") }
    }
    var isDark: Bool {
        didSet { UserDefaults.standard.set(isDark, forKey: "infpad.isDark") }
    }
    var order: Int {
        didSet { UserDefaults.standard.set(order, forKey: "infpad.order") }
    }
    var preferLocalOCR: Bool {
        didSet { UserDefaults.standard.set(preferLocalOCR, forKey: "infpad.preferLocalOCR") }
    }

    // Navigation & AirPlay / HDMI Presentation state
    var activeTab: InfPadTab = .calculator
    var externalOutputMode: ExternalOutputMode = .slide
    var currentSlideIndex: Int = 0
    var isAirPlayClean: Bool = false
    var slideDrawings: [Int: PKDrawing] = [:]
    var slideAnnotationTool: SlideInkTool = .pen
    var slidePencilOnly: Bool = true
    var returnedFromSlides: Bool = false

    // Calculator state (100% real Lean 4 FastLC evaluation, generic clean opening screen!)
    var drawing = PKDrawing()
    var toolMode: DrawingToolMode = .pen
    var expressionText: String = ""
    var recognizedExpr: String? = nil
    var ocrModel: String? = nil
    var ocrMs: Double? = nil
    var leanMs: Double? = nil

    var evalResult: EvalResponse? = nil
    var sliderN: Double = 100
    var isScrubbingN: Bool = false
    var showApprox: Bool = false
    var expandExactTail: Bool = false

    var health: HealthResponse? = nil
    var isConnected: Bool = false
    var isCheckingHealth: Bool = false
    var isOcrRunning: Bool = false
    var isEvaluating: Bool = false
    var errorMessage: String? = nil
    var showSettings: Bool = false
    var canUndo: Bool = false
    var canRedo: Bool = false

    var history: [HistoryEntry] = []

    let canvasController = InfCanvasController()
    private let api = InfAPIClient()
    private let historyDir: URL
    private var sliderDebounceTask: Task<Void, Never>? = nil
    private var evalGeneration: UInt64 = 0

    private func nextGeneration() -> UInt64 {
        evalGeneration &+= 1
        return evalGeneration
    }

    var theme: InfTheme { InfTheme(isDark: isDark) }

    init() {
        var savedURL = UserDefaults.standard.string(forKey: "infpad.serverURL") ?? ""
        if savedURL.isEmpty || savedURL.contains("mac.tailbf1ac1.ts.net") {
            savedURL = InfPadPresets.defaultServerURL
            UserDefaults.standard.set(savedURL, forKey: "infpad.serverURL")
        }
        self.serverURL = savedURL
        self.isDark = UserDefaults.standard.bool(forKey: "infpad.isDark")
        self.preferLocalOCR = UserDefaults.standard.bool(forKey: "infpad.preferLocalOCR")
        let savedOrder = UserDefaults.standard.integer(forKey: "infpad.order")
        self.order = (4...24).contains(savedOrder) ? savedOrder : 10

        let appSupport = FileManager.default.urls(for: .applicationSupportDirectory, in: .userDomainMask).first
            ?? FileManager.default.temporaryDirectory
        self.historyDir = appSupport.appendingPathComponent("InfPad/history", isDirectory: true)
        try? FileManager.default.createDirectory(at: historyDir, withIntermediateDirectories: true)

        loadHistoryFromDisk()
    }

    func bootstrap() async {
        let args = ProcessInfo.processInfo.arguments
        if let apiIdx = args.firstIndex(of: "-apiBase"), apiIdx + 1 < args.count {
            serverURL = args[apiIdx + 1]
        }
        if args.contains("-preferLocalOCR") {
            preferLocalOCR = true
        }
        if let tabIdx = args.firstIndex(of: "-demoTab"), tabIdx + 1 < args.count {
            switch args[tabIdx + 1].lowercased() {
            case "slides": activeTab = .slides
            case "split": activeTab = .split
            default: activeTab = .calculator
            }
        }
        if let slideIdx = args.firstIndex(of: "-demoSlide"), slideIdx + 1 < args.count,
           let idx = Int(args[slideIdx + 1]) {
            currentSlideIndex = max(0, min(SlideDeck.slides.count - 1, idx))
        }
        if args.contains("-demoAirPlayClean") {
            isAirPlayClean = true
        }

        await checkHealth()

        if args.contains("-demoInk") {
            activeTab = .calculator
            drawing = InfCanvasController.makeDemoDrawing()
            syncUndoState()
            await evaluateInk()
            return
        }

        if let exprIdx = args.firstIndex(of: "-demoExpr"), exprIdx + 1 < args.count {
            expressionText = args[exprIdx + 1]
            await evaluateExpression(expressionText, saveToHistory: true)
            return
        }
        // Clean generic launch: keep expressionText empty & evalResult nil until user draws, types, or taps a starter chip.
    }

    // MARK: - Slide Navigation & Cross-Pane Demo Jump

    func nextSlide() {
        if currentSlideIndex + 1 < SlideDeck.slides.count {
            currentSlideIndex += 1
        }
    }

    func prevSlide() {
        if currentSlideIndex > 0 {
            currentSlideIndex -= 1
        }
    }

    func jumpToCalculator(expr: String? = nil, clearCanvasForDrawing: Bool = false) {
        if activeTab == .slides {
            returnedFromSlides = true
            activeTab = .calculator
        }
        // In Split mode, stay in Split mode so the adjacent Calculator pane evaluates immediately!
        if clearCanvasForDrawing {
            clearCanvas()
            expressionText = ""
            evalResult = nil
            return
        }
        if let expr, !expr.isEmpty {
            expressionText = expr
            Task { await evaluateExpression(expr, saveToHistory: true) }
        }
    }

    func returnToSlides() {
        activeTab = .slides
    }

    func clearSlideDrawing(index: Int) {
        slideDrawings[index] = PKDrawing()
    }

    // MARK: - Canvas Controls

    func syncUndoState() {
        canUndo = canvasController.canUndo
        canRedo = canvasController.canRedo
    }

    func undo() {
        canvasController.undo()
        syncUndoState()
    }

    func redo() {
        canvasController.redo()
        syncUndoState()
    }

    func clearCanvas() {
        drawing = PKDrawing()
        errorMessage = nil
        syncUndoState()
    }

    func checkHealth() async {
        isCheckingHealth = true
        defer { isCheckingHealth = false }
        do {
            let (h, resolved) = try await api.health(baseURL: serverURL)
            health = h
            isConnected = h.ok
            if resolved != serverURL {
                serverURL = resolved
            }
        } catch {
            health = nil
            isConnected = false
        }
    }

    /// 3-Tier OCR -> REAL Lean 4 FastLC pipeline:
    /// Tier 1: POST /ocr-eval (Gemini Vision -> Lean 4)
    /// Tier 1.5: Mac server silently falls back to macOS Vision -> Lean 4
    /// Tier 2: On-device Apple Vision Neural Engine OCR -> GET /eval on REAL Lean 4!
    func evaluateInk() async {
        guard !drawing.strokes.isEmpty else {
            errorMessage = "Draw an expression on the canvas first, or tap a starter chip below."
            return
        }
        guard let pngData = canvasController.exportWhitePaperPNG(drawing: drawing) else {
            errorMessage = "Could not render canvas ink to PNG."
            return
        }

        sliderDebounceTask?.cancel()
        sliderDebounceTask = nil
        let gen = nextGeneration()
        let drawingCopy = drawing

        isOcrRunning = true
        errorMessage = nil
        expandExactTail = false
        defer {
            if gen == evalGeneration {
                isOcrRunning = false
            }
        }

        if preferLocalOCR {
            await runOnDeviceVisionThenLeanEval(pngData: pngData, drawingCopy: drawingCopy, gen: gen)
            return
        }

        do {
            let resp = try await api.ocrEvaluate(
                baseURL: serverURL,
                pngData: pngData,
                bigN: sliderN,
                order: order
            )
            guard gen == evalGeneration else { return }

            ocrMs = resp.ocrMs ?? resp.ocr?.ocrMs
            leanMs = resp.serverMs ?? resp.eval?.serverMs
            ocrModel = resp.model ?? resp.ocr?.model
            recognizedExpr = resp.recognizedExpr ?? resp.ocr?.rawExpr

            let normalized = (resp.normalizedExpr ?? resp.ocr?.expr ?? "").trimmingCharacters(in: .whitespacesAndNewlines)
            if !normalized.isEmpty {
                expressionText = normalized
            }

            if let ev = resp.eval {
                evalResult = ev
                if !ev.ok {
                    errorMessage = ev.error ?? resp.error ?? "Lean 4 could not evaluate recognized expression."
                } else {
                    appendHistory(
                        expression: normalized.isEmpty ? expressionText : normalized,
                        recognizedExpr: recognizedExpr,
                        eval: ev,
                        ocrMs: ocrMs,
                        leanMs: leanMs,
                        drawingSnapshot: drawingCopy
                    )
                }
            } else {
                errorMessage = resp.error ?? "No expression recognized."
            }
            isConnected = true
        } catch {
            guard gen == evalGeneration else { return }
            await runOnDeviceVisionThenLeanEval(pngData: pngData, drawingCopy: drawingCopy, gen: gen)
        }
    }

    private func runOnDeviceVisionThenLeanEval(pngData: Data, drawingCopy: PKDrawing, gen: UInt64) async {
        let rec = await LocalHandwritingOCR.recognize(pngData: pngData)
        guard gen == evalGeneration else { return }

        ocrMs = rec.ocrMs
        ocrModel = "apple-vision"
        recognizedExpr = rec.rawExpr

        guard !rec.normalizedExpr.isEmpty else {
            errorMessage = "Could not recognize math ink. Try writing larger or use the text field."
            return
        }
        expressionText = rec.normalizedExpr

        do {
            let ev = try await api.evaluate(
                baseURL: serverURL,
                expr: rec.normalizedExpr,
                bigN: sliderN,
                order: order
            )
            guard gen == evalGeneration else { return }
            evalResult = ev
            leanMs = ev.serverMs
            isConnected = true
            if !ev.ok {
                errorMessage = ev.error ?? "Lean 4 could not evaluate recognized expression."
            } else {
                appendHistory(
                    expression: rec.normalizedExpr,
                    recognizedExpr: rec.rawExpr,
                    eval: ev,
                    ocrMs: rec.ocrMs,
                    leanMs: ev.serverMs,
                    drawingSnapshot: drawingCopy
                )
            }
        } catch {
            guard gen == evalGeneration else { return }
            isConnected = false
            errorMessage = "Recognized '\(rec.normalizedExpr)', but Lean 4 server is unreachable: \(error.localizedDescription)"
        }
    }

    func evaluateExpression(_ expr: String? = nil, saveToHistory: Bool = true) async {
        let target = (expr ?? expressionText).trimmingCharacters(in: .whitespacesAndNewlines)
        guard !target.isEmpty else {
            errorMessage = "Enter an expression to evaluate."
            return
        }

        sliderDebounceTask?.cancel()
        sliderDebounceTask = nil
        let gen = nextGeneration()

        expressionText = target
        isEvaluating = true
        errorMessage = nil
        expandExactTail = false
        defer {
            if gen == evalGeneration {
                isEvaluating = false
            }
        }

        do {
            let ev = try await api.evaluate(
                baseURL: serverURL,
                expr: target,
                bigN: sliderN,
                order: order
            )
            guard gen == evalGeneration else { return }

            evalResult = ev
            leanMs = ev.serverMs
            ocrMs = nil
            recognizedExpr = nil
            isConnected = true

            if !ev.ok {
                errorMessage = ev.error ?? "Evaluation failed."
            } else if saveToHistory {
                appendHistory(
                    expression: target,
                    recognizedExpr: nil,
                    eval: ev,
                    ocrMs: nil,
                    leanMs: ev.serverMs,
                    drawingSnapshot: nil
                )
            }
        } catch {
            guard gen == evalGeneration else { return }
            isConnected = false
            errorMessage = error.localizedDescription
        }
    }

    func selectStarterChip(_ chip: StarterChip) async {
        expressionText = chip.expr
        await evaluateExpression(chip.expr, saveToHistory: true)
    }

    func scheduleDebouncedPlotUpdate() {
        guard evalResult?.isFunction == true || evalResult?.isHeatmap == true else { return }
        sliderDebounceTask?.cancel()
        sliderDebounceTask = Task { [weak self] in
            try? await Task.sleep(for: .milliseconds(120))
            guard !Task.isCancelled, let self else { return }
            await self.performSliderEval()
        }
    }

    func commitSliderN() async {
        sliderDebounceTask?.cancel()
        sliderDebounceTask = nil
        await performSliderEval()
    }

    private func performSliderEval() async {
        guard let currentExpr = evalResult?.input ?? (expressionText.isEmpty ? nil : expressionText) else { return }
        guard !currentExpr.isEmpty else { return }
        let gen = nextGeneration()
        let requestedN = sliderN
        do {
            let ev = try await api.evaluate(
                baseURL: serverURL,
                expr: currentExpr,
                bigN: requestedN,
                order: order
            )
            guard gen == evalGeneration else { return }
            if ev.ok {
                evalResult = ev
                leanMs = ev.serverMs
                isConnected = true
            }
        } catch {
            // Local finite preview stays visible if network blips during slider scrub
        }
    }

    func displayedFiniteValue() -> Double? {
        guard let ev = evalResult, ev.ok else { return nil }
        if isScrubbingN {
            return ev.localEvalFinite(at: sliderN)
        }
        if let serverN = ev.eval_N, abs(serverN - sliderN.rounded()) < 0.5, let serverVal = ev.eval_finite {
            return serverVal
        }
        return ev.localEvalFinite(at: sliderN) ?? ev.eval_finite
    }

    func insertSymbol(_ sym: String) {
        expressionText.append(sym)
    }

    // MARK: - History Persistence

    func thumbnailImage(for entry: HistoryEntry) -> UIImage? {
        guard entry.hasDrawing else { return nil }
        let url = historyDir.appendingPathComponent("\(entry.id.uuidString).png")
        guard let data = try? Data(contentsOf: url) else { return nil }
        return UIImage(data: data)
    }

    func loadHistoryEntry(_ entry: HistoryEntry) async {
        expressionText = entry.expression
        recognizedExpr = entry.recognizedExpr
        ocrMs = entry.ocrMs
        leanMs = entry.leanMs
        errorMessage = nil
        expandExactTail = false

        if entry.hasDrawing {
            let drawingURL = historyDir.appendingPathComponent("\(entry.id.uuidString).pkdrawing")
            if let data = try? Data(contentsOf: drawingURL), let restored = try? PKDrawing(data: data) {
                drawing = restored
                syncUndoState()
            }
        }

        if let snap = entry.evalSnapshot {
            evalResult = snap
        }
        await evaluateExpression(entry.expression, saveToHistory: false)
    }

    func clearHistory() {
        history.removeAll()
        if let files = try? FileManager.default.contentsOfDirectory(at: historyDir, includingPropertiesForKeys: nil) {
            for f in files { try? FileManager.default.removeItem(at: f) }
        }
        saveHistoryIndex()
    }

    private func appendHistory(
        expression: String,
        recognizedExpr: String?,
        eval: EvalResponse,
        ocrMs: Double?,
        leanMs: Double?,
        drawingSnapshot: PKDrawing?
    ) {
        if drawingSnapshot == nil, let first = history.first, first.expression == expression, !first.hasDrawing {
            return
        }

        let id = UUID()
        var hasDrawing = false
        if let d = drawingSnapshot, !d.strokes.isEmpty {
            let drawingURL = historyDir.appendingPathComponent("\(id.uuidString).pkdrawing")
            try? d.dataRepresentation().write(to: drawingURL)
            if let thumb = canvasController.exportThumbnailPNG(drawing: d) {
                let thumbURL = historyDir.appendingPathComponent("\(id.uuidString).png")
                try? thumb.write(to: thumbURL)
            }
            hasDrawing = true
        }

        let entry = HistoryEntry(
            id: id,
            timestamp: Date(),
            expression: expression,
            recognizedExpr: recognizedExpr,
            exactSummary: eval.exact ?? eval.approx ?? "",
            regime: eval.regime,
            ocrMs: ocrMs,
            leanMs: leanMs,
            hasDrawing: hasDrawing,
            evalSnapshot: eval
        )

        history.insert(entry, at: 0)
        if history.count > 24 {
            let removed = history.removeLast()
            try? FileManager.default.removeItem(at: historyDir.appendingPathComponent("\(removed.id.uuidString).pkdrawing"))
            try? FileManager.default.removeItem(at: historyDir.appendingPathComponent("\(removed.id.uuidString).png"))
        }
        saveHistoryIndex()
    }

    private func historyIndexURL() -> URL {
        historyDir.appendingPathComponent("history.json")
    }

    private func saveHistoryIndex() {
        if let data = try? JSONEncoder().encode(history) {
            try? data.write(to: historyIndexURL())
        }
    }

    private func loadHistoryFromDisk() {
        guard let data = try? Data(contentsOf: historyIndexURL()),
              let decoded = try? JSONDecoder().decode([HistoryEntry].self, from: data) else {
            return
        }
        history = decoded
    }
}
