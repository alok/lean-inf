import Foundation
import Observation
import PencilKit
import SwiftUI

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

    var drawing = PKDrawing()
    var toolMode: DrawingToolMode = .pen
    var expressionText: String = "1/(1+exp(-Hx))"
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

    var theme: InfTheme { InfTheme(isDark: isDark) }

    init() {
        let savedURL = UserDefaults.standard.string(forKey: "infpad.serverURL")
        self.serverURL = (savedURL?.isEmpty == false ? savedURL! : InfPadPresets.defaultServerURL)
        self.isDark = UserDefaults.standard.bool(forKey: "infpad.isDark")
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

        await checkHealth()

        if args.contains("-demoInk") {
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

        // On clean startup, pre-evaluate starter expression so the right inspector looks alive immediately
        if evalResult == nil {
            await evaluateExpression(expressionText, saveToHistory: false)
        }
    }

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
            let h = try await api.health(baseURL: serverURL)
            health = h
            isConnected = h.ok
        } catch {
            health = nil
            isConnected = false
        }
    }

    func evaluateInk() async {
        guard !drawing.strokes.isEmpty else {
            errorMessage = "Draw an expression on the canvas first, or tap a starter chip below."
            return
        }
        guard let pngData = canvasController.exportWhitePaperPNG(drawing: drawing) else {
            errorMessage = "Could not render canvas ink to PNG."
            return
        }

        isOcrRunning = true
        errorMessage = nil
        expandExactTail = false
        defer { isOcrRunning = false }

        do {
            let resp = try await api.ocrEvaluate(
                baseURL: serverURL,
                pngData: pngData,
                bigN: sliderN,
                order: order
            )
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
                        drawingSnapshot: drawing
                    )
                }
            } else {
                errorMessage = resp.error ?? "No expression recognized."
            }
            isConnected = true
        } catch {
            errorMessage = error.localizedDescription
        }
    }

    func evaluateExpression(_ expr: String? = nil, saveToHistory: Bool = true) async {
        let target = (expr ?? expressionText).trimmingCharacters(in: .whitespacesAndNewlines)
        guard !target.isEmpty else {
            errorMessage = "Enter an expression to evaluate."
            return
        }
        expressionText = target
        isEvaluating = true
        errorMessage = nil
        expandExactTail = false
        defer { isEvaluating = false }

        do {
            let ev = try await api.evaluate(
                baseURL: serverURL,
                expr: target,
                bigN: sliderN,
                order: order
            )
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
            errorMessage = error.localizedDescription
        }
    }

    func selectStarterChip(_ chip: StarterChip) async {
        expressionText = chip.expr
        await evaluateExpression(chip.expr, saveToHistory: true)
    }

    func scheduleDebouncedPlotUpdate() {
        guard evalResult?.isFunction == true else { return }
        sliderDebounceTask?.cancel()
        sliderDebounceTask = Task { [weak self] in
            try? await Task.sleep(for: .milliseconds(120))
            guard !Task.isCancelled, let self else { return }
            await self.commitSliderN()
        }
    }

    func commitSliderN() async {
        sliderDebounceTask?.cancel()
        sliderDebounceTask = nil
        guard let currentExpr = evalResult?.input ?? (expressionText.isEmpty ? nil : expressionText) else { return }
        guard !currentExpr.isEmpty else { return }
        let requestedN = sliderN
        do {
            let ev = try await api.evaluate(
                baseURL: serverURL,
                expr: currentExpr,
                bigN: requestedN,
                order: order
            )
            // Only apply if user hasn't switched expressions while in-flight
            if ev.ok && (evalResult?.input == nil || evalResult?.input == currentExpr) {
                evalResult = ev
                leanMs = ev.serverMs
            }
        } catch {
            // Local finite preview stays visible even if network blips during slider release
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
        // Avoid back-to-back duplicate non-drawing entries
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
