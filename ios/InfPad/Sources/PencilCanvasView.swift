import PencilKit
import SwiftUI
import UIKit

enum DrawingToolMode: String, CaseIterable, Identifiable {
    case pen
    case eraser
    var id: String { rawValue }
}

final class InfCanvasController {
    weak var canvasView: PKCanvasView?

    func undo() {
        canvasView?.undoManager?.undo()
    }

    func redo() {
        canvasView?.undoManager?.redo()
    }

    var canUndo: Bool {
        canvasView?.undoManager?.canUndo ?? false
    }

    var canRedo: Bool {
        canvasView?.undoManager?.canRedo ?? false
    }

    /// Exports handwritten PencilKit strokes as a crisp, high-DPI dark-ink-on-white-paper PNG for Gemini Vision OCR.
    func exportWhitePaperPNG(drawing: PKDrawing, maxPixels: CGFloat = 1400) -> Data? {
        guard !drawing.strokes.isEmpty else { return nil }
        let rawBounds = drawing.bounds
        guard rawBounds.width > 1 || rawBounds.height > 1 else { return nil }

        // Generous white margin around strokes so superscripts and fractions stay crystal clear
        let pad: CGFloat = 44
        var region = rawBounds.insetBy(dx: -pad, dy: -pad)
        if region.width < 280 {
            let extra = (280 - region.width) / 2
            region = region.insetBy(dx: -extra, dy: 0)
        }
        if region.height < 140 {
            let extra = (140 - region.height) / 2
            region = region.insetBy(dx: 0, dy: -extra)
        }

        let maxDim = max(region.width, region.height)
        let scale = min(2.5, max(1.0, maxPixels / maxDim))
        let pixelSize = CGSize(
            width: max(64, floor(region.width * scale)),
            height: max(64, floor(region.height * scale))
        )

        // Force light interface style so PencilKit always renders dark ink, even in Soft Slate Dark mode
        var inkImage: UIImage?
        UITraitCollection(userInterfaceStyle: .light).performAsCurrent {
            inkImage = drawing.image(from: region, scale: scale)
        }

        let format = UIGraphicsImageRendererFormat()
        format.scale = 1.0
        format.opaque = true

        let rendered = UIGraphicsImageRenderer(size: pixelSize, format: format).image { ctx in
            UIColor.white.setFill()
            ctx.fill(CGRect(origin: .zero, size: pixelSize))
            inkImage?.draw(in: CGRect(origin: .zero, size: pixelSize))
        }
        return rendered.pngData()
    }

    /// Generates a small thumbnail PNG for the history strip.
    func exportThumbnailPNG(drawing: PKDrawing) -> Data? {
        exportWhitePaperPNG(drawing: drawing, maxPixels: 280)
    }

    /// Creates clean vector PencilKit ink strokes spelling `dstep(0)` for automated demo verification.
    static func makeDemoDrawing() -> PKDrawing {
        let ink = PKInk(.pen, color: UIColor(red: 0.067, green: 0.094, blue: 0.153, alpha: 1.0))

        func stroke(_ pts: [(CGFloat, CGFloat)], width: CGFloat = 6.5) -> PKStroke {
            let controlPoints = pts.enumerated().map { idx, p in
                PKStrokePoint(
                    location: CGPoint(x: p.0, y: p.1),
                    timeOffset: TimeInterval(idx) * 0.015,
                    size: CGSize(width: width, height: width),
                    opacity: 1.0,
                    force: 1.0,
                    azimuth: 0,
                    altitude: .pi / 2
                )
            }
            let path = PKStrokePath(controlPoints: controlPoints, creationDate: Date())
            return PKStroke(ink: ink, path: path)
        }

        // Crisp handwritten-style "dstep(0)" strokes centered around x: 80..540, y: 120..240
        let strokes: [PKStroke] = [
            // 'd' bowl + stem
            stroke([(128, 172), (105, 168), (92, 184), (94, 206), (112, 214), (128, 202)]),
            stroke([(130, 125), (130, 215)]),
            // 's'
            stroke([(186, 170), (164, 168), (156, 180), (176, 192), (186, 205), (164, 214), (152, 208)]),
            // 't' stem + crossbar
            stroke([(214, 134), (214, 212), (226, 214)]),
            stroke([(198, 166), (234, 166)]),
            // 'e'
            stroke([(248, 190), (282, 188), (278, 172), (258, 168), (246, 184), (252, 208), (280, 212)]),
            // 'p' stem + bowl
            stroke([(302, 168), (302, 250)]),
            stroke([(302, 176), (324, 168), (340, 182), (336, 204), (316, 212), (302, 204)]),
            // '('
            stroke([(376, 138), (360, 166), (358, 198), (376, 226)]),
            // '0'
            stroke([(416, 146), (398, 162), (394, 192), (404, 216), (424, 216), (436, 192), (432, 160), (416, 146)]),
            // ')'
            stroke([(456, 138), (472, 166), (474, 198), (456, 226)]),
        ]
        return PKDrawing(strokes: strokes)
    }
}

struct PencilCanvasView: UIViewRepresentable {
    @Binding var drawing: PKDrawing
    var toolMode: DrawingToolMode
    var inkColor: UIColor
    var controller: InfCanvasController
    var onDrawingChanged: () -> Void

    func makeCoordinator() -> Coordinator {
        Coordinator(parent: self)
    }

    func makeUIView(context: Context) -> PKCanvasView {
        let canvas = PKCanvasView()
        canvas.backgroundColor = .clear
        canvas.isOpaque = false
        canvas.drawingPolicy = .anyInput
        canvas.alwaysBounceVertical = false
        canvas.alwaysBounceHorizontal = false
        canvas.showsVerticalScrollIndicator = false
        canvas.showsHorizontalScrollIndicator = false
        canvas.delegate = context.coordinator
        canvas.drawing = drawing
        canvas.tool = currentTool()
        controller.canvasView = canvas
        return canvas
    }

    func updateUIView(_ canvas: PKCanvasView, context: Context) {
        context.coordinator.parent = self
        controller.canvasView = canvas

        let desiredTool = currentTool()
        canvas.tool = desiredTool

        if !context.coordinator.isInternalUpdate && canvas.drawing.dataRepresentation() != drawing.dataRepresentation() {
            context.coordinator.isInternalUpdate = true
            canvas.drawing = drawing
            context.coordinator.isInternalUpdate = false
        }
    }

    private func currentTool() -> PKTool {
        switch toolMode {
        case .pen:
            return PKInkingTool(.pen, color: inkColor, width: 6.5)
        case .eraser:
            return PKEraserTool(.vector)
        }
    }

    final class Coordinator: NSObject, PKCanvasViewDelegate {
        var parent: PencilCanvasView
        var isInternalUpdate = false

        init(parent: PencilCanvasView) {
            self.parent = parent
        }

        func canvasViewDrawingDidChange(_ canvasView: PKCanvasView) {
            guard !isInternalUpdate else { return }
            isInternalUpdate = true
            parent.drawing = canvasView.drawing
            parent.onDrawingChanged()
            isInternalUpdate = false
        }
    }
}

/// Subtle warm dot-grid backdrop underneath the transparent PKCanvasView (excluded from OCR PNG).
struct PaperDotGrid: View {
    let dotColor: Color
    let spacing: CGFloat = 32

    var body: some View {
        Canvas { context, size in
            let cols = Int(size.width / spacing)
            let rows = Int(size.height / spacing)
            let radius: CGFloat = 1.25
            for r in 1...max(1, rows) {
                for c in 1...max(1, cols) {
                    let pt = CGPoint(x: CGFloat(c) * spacing, y: CGFloat(r) * spacing)
                    let rect = CGRect(x: pt.x - radius, y: pt.y - radius, width: radius * 2, height: radius * 2)
                    context.fill(Path(ellipseIn: rect), with: .color(dotColor))
                }
            }
        }
        .allowsHitTesting(false)
    }
}
