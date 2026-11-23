import SwiftUI

enum PlotZoomMode: String, CaseIterable, Identifiable {
    case macro
    case micro

    var id: String { rawValue }
}

/// Astigmatism-friendly interactive plot card for free-variable `f(x)` expressions evaluated in Lean 4.
struct FunctionPlotCard: View {
    let eval: EvalResponse
    let plot: FnPlot
    let theme: InfTheme
    let currentN: Int
    let latencyText: String?

    @State private var zoomMode: PlotZoomMode = .macro
    @State private var draggedPoint: (x: Double, y: Double)? = nil
    @State private var selectedProbe: FnProbe? = nil

    private var activePoints: [(Double, Double)] {
        let raw: [[Double]]
        if zoomMode == .micro, let zp = plot.zoom_points, !zp.isEmpty {
            raw = zp
        } else {
            raw = plot.points
        }
        return raw.compactMap { pair in
            guard pair.count >= 2, pair[0].isFinite, pair[1].isFinite else { return nil }
            return (pair[0], pair[1])
        }
    }

    private var xRange: (min: Double, max: Double) {
        if zoomMode == .micro, let x0 = plot.zoom_x_min, let x1 = plot.zoom_x_max, x1 > x0 {
            return (x0, x1)
        }
        let lo = plot.x_min
        let hi = plot.x_max > lo ? plot.x_max : lo + 2
        return (lo, hi)
    }

    private var yRange: (min: Double, max: Double) {
        let rawMin: Double
        let rawMax: Double
        if zoomMode == .micro, let y0 = plot.zoom_y_min, let y1 = plot.zoom_y_max {
            rawMin = y0
            rawMax = y1
        } else {
            rawMin = plot.y_min
            rawMax = plot.y_max
        }
        let span = rawMax - rawMin
        if span < 1e-9 {
            return (rawMin - 1.0, rawMax + 1.0)
        }
        // Subtle 7% vertical breathing room so flat plateaus at y = 0 and y = 1 stay crisp inside frame
        let pad = span * 0.07
        return (rawMin - pad, rawMax + pad)
    }

    private var rawYBounds: (min: Double, max: Double) {
        if zoomMode == .micro, let y0 = plot.zoom_y_min, let y1 = plot.zoom_y_max {
            return (y0, y1)
        }
        return (plot.y_min, plot.y_max)
    }

    private var pointAtZero: (Double, Double)? {
        guard !activePoints.isEmpty else { return nil }
        guard let closest = activePoints.min(by: { abs($0.0) < abs($1.0) }) else { return nil }
        let tol = max(1e-9, (xRange.max - xRange.min) * 1e-4)
        return abs(closest.0) <= tol ? closest : nil
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            // Card Header: Badge + Macro/Micro Toggle + Latency
            HStack(spacing: 10) {
                let style = theme.regimeStyle(eval.regime)
                Text(style.label)
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .foregroundStyle(style.fg)
                    .padding(.horizontal, 10)
                    .padding(.vertical, 5)
                    .background(style.bg, in: Capsule())

                if let latencyText {
                    Text(latencyText)
                        .font(.system(size: 15, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 4)
                        .background(theme.elevatedCard, in: Capsule())
                        .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                }

                Spacer()

                // Macro [-1, 1] vs Micro ±8ε segmented pill
                if plot.hasZoom {
                    HStack(spacing: 3) {
                        zoomPill(mode: .macro, label: "Macro [-1, 1]")
                        zoomPill(mode: .micro, label: "Micro ±8ε")
                    }
                    .padding(3)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 11, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 11, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }
            }

            // Interactive High-Contrast Canvas Plot
            plotCanvasView
                .frame(height: 220)
                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 16, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 16, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1.25))

            // Compact Exact Lean 4 FastLC Probes Strip
            if let probes = eval.probes, !probes.isEmpty {
                probesSection(probes)
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
        .onChange(of: eval.input) { _, _ in
            draggedPoint = nil
            selectedProbe = nil
        }
    }

    private func zoomPill(mode: PlotZoomMode, label: String) -> some View {
        let active = zoomMode == mode
        return Button {
            withAnimation(.easeInOut(duration: 0.16)) {
                zoomMode = mode
                draggedPoint = nil
            }
        } label: {
            Text(label)
                .font(.system(size: 15, weight: .bold, design: .rounded))
                .foregroundStyle(active ? .white : theme.primaryInk)
                .padding(.horizontal, 12)
                .padding(.vertical, 6)
                .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 8, style: .continuous))
        }
        .buttonStyle(.plain)
    }

    // MARK: - SwiftUI Canvas + Drag Crosshair

    private var plotCanvasView: some View {
        GeometryReader { geo in
            let insetLeft: CGFloat = 58
            let insetRight: CGFloat = 20
            let insetTop: CGFloat = 18
            let insetBottom: CGFloat = 34
            let plotRect = CGRect(
                x: insetLeft,
                y: insetTop,
                width: max(40, geo.size.width - insetLeft - insetRight),
                height: max(40, geo.size.height - insetTop - insetBottom)
            )
            let xr = xRange
            let yr = yRange
            let pts = activePoints

            ZStack(alignment: .topLeading) {
                Canvas { ctx, _ in
                    func mapX(_ x: Double) -> CGFloat {
                        let t = (x - xr.min) / max(1e-12, xr.max - xr.min)
                        return plotRect.minX + CGFloat(t) * plotRect.width
                    }

                    func mapY(_ y: Double) -> CGFloat {
                        let t = (y - yr.min) / max(1e-12, yr.max - yr.min)
                        return plotRect.maxY - CGFloat(t) * plotRect.height
                    }

                    // 1. Subtle horizontal gridlines & Y ticks (yMax, mid, yMin)
                    let rawY = rawYBounds
                    let yMid = (rawY.min + rawY.max) / 2.0
                    let yTicks = abs(rawY.max - rawY.min) < 1e-9
                        ? [rawY.min]
                        : [rawY.min, yMid, rawY.max]

                    for yVal in yTicks {
                        let py = mapY(yVal)
                        var gridPath = Path()
                        gridPath.move(to: CGPoint(x: plotRect.minX, y: py))
                        gridPath.addLine(to: CGPoint(x: plotRect.maxX, y: py))
                        ctx.stroke(gridPath, with: .color(theme.borderSubtle), lineWidth: 1)

                        let label = Text(formatAxisTick(yVal))
                            .font(.system(size: 13, weight: .medium, design: .monospaced))
                            .foregroundColor(theme.secondaryInk)
                        ctx.draw(label, at: CGPoint(x: plotRect.minX - 8, y: py), anchor: .trailing)
                    }

                    // 2. X baseline (y = 0 if visible)
                    if yr.min <= 0 && yr.max >= 0 {
                        let y0 = mapY(0)
                        var base = Path()
                        base.move(to: CGPoint(x: plotRect.minX, y: y0))
                        base.addLine(to: CGPoint(x: plotRect.maxX, y: y0))
                        ctx.stroke(base, with: .color(theme.secondaryInk.opacity(0.32)), lineWidth: 1)
                    }

                    // 3. Dashed vertical guide at x = 0
                    if xr.min <= 0 && xr.max >= 0 {
                        let x0 = mapX(0)
                        var guide = Path()
                        guide.move(to: CGPoint(x: x0, y: plotRect.minY))
                        guide.addLine(to: CGPoint(x: x0, y: plotRect.maxY))
                        ctx.stroke(
                            guide,
                            with: .color(theme.secondaryInk.opacity(0.45)),
                            style: StrokeStyle(lineWidth: 1.25, dash: [5, 5])
                        )
                    }

                    // 4. Plot border frame (bottom + left axes)
                    var axes = Path()
                    axes.move(to: CGPoint(x: plotRect.minX, y: plotRect.minY))
                    axes.addLine(to: CGPoint(x: plotRect.minX, y: plotRect.maxY))
                    axes.addLine(to: CGPoint(x: plotRect.maxX, y: plotRect.maxY))
                    ctx.stroke(axes, with: .color(theme.secondaryInk.opacity(0.42)), lineWidth: 1.25)

                    // 5. X ticks (left, center 0, right)
                    let xLabels: [(Double, String)] = zoomMode == .micro
                        ? [(xr.min, "-8ε"), (0.0, "0"), (xr.max, "+8ε")]
                        : [(xr.min, formatAxisTick(xr.min)), (0.0, "0"), (xr.max, formatAxisTick(xr.max))]
                    for (xv, lbl) in xLabels {
                        let px = mapX(xv)
                        let tickText = Text(lbl)
                            .font(.system(size: 13, weight: .semibold, design: .monospaced))
                            .foregroundColor(theme.secondaryInk)
                        ctx.draw(tickText, at: CGPoint(x: px, y: plotRect.maxY + 15), anchor: .center)
                    }

                    // 6. Clipped continuous segments + discontinuity-safe fill + high-contrast 2.8pt curve
                    if pts.count >= 2 {
                        let maxJump = plotRect.height * 0.65
                        var segments: [[CGPoint]] = []
                        var currentSeg: [CGPoint] = []
                        var prevRawY: Double? = nil
                        let ySpan = max(1e-9, yr.max - yr.min)

                        for (x, y) in pts {
                            let px = mapX(x)
                            let py = mapY(y)
                            let isPoleSignFlip = (prevRawY != nil) && (
                                (prevRawY! < yr.min && y > yr.max) ||
                                (prevRawY! > yr.max && y < yr.min) ||
                                (prevRawY! * y < 0 && abs(y - prevRawY!) > 0.55 * ySpan)
                            )
                            if let lastPt = currentSeg.last, (abs(py - lastPt.y) > maxJump || isPoleSignFlip) {
                                if !currentSeg.isEmpty { segments.append(currentSeg) }
                                currentSeg = [CGPoint(x: px, y: py)]
                            } else {
                                currentSeg.append(CGPoint(x: px, y: py))
                            }
                            prevRawY = y
                        }
                        if !currentSeg.isEmpty { segments.append(currentSeg) }

                        var clipped = ctx
                        clipped.clip(to: Path(plotRect))

                        // Only draw soft area fill when curve is a single continuous branch (zero diagonal pole artifacts!)
                        if segments.count == 1, let seg = segments.first, seg.count >= 2 {
                            let baselineY = (yr.min <= 0 && yr.max >= 0) ? mapY(0) : plotRect.maxY
                            var fillPath = Path()
                            fillPath.move(to: seg[0])
                            for pt in seg.dropFirst() {
                                fillPath.addLine(to: pt)
                            }
                            fillPath.addLine(to: CGPoint(x: seg.last!.x, y: baselineY))
                            fillPath.addLine(to: CGPoint(x: seg.first!.x, y: baselineY))
                            fillPath.closeSubpath()
                            clipped.fill(fillPath, with: .color(theme.accentCobalt.opacity(0.08)))
                        }

                        var curve = Path()
                        for seg in segments where seg.count >= 2 {
                            curve.move(to: seg[0])
                            for pt in seg.dropFirst() {
                                curve.addLine(to: pt)
                            }
                        }

                        clipped.stroke(
                            curve,
                            with: .color(theme.accentCobalt),
                            style: StrokeStyle(lineWidth: 2.8, lineCap: .round, lineJoin: .round)
                        )
                    }

                    // 7. Highlighted dot at (0, f_N(0)) only when x = 0 is actually sampled & in-frame
                    if let p0 = pointAtZero, xr.min <= p0.0, p0.0 <= xr.max, yr.min <= p0.1, p0.1 <= yr.max {
                        let cx = mapX(p0.0)
                        let cy = mapY(p0.1)
                        let outer = CGRect(x: cx - 6, y: cy - 6, width: 12, height: 12)
                        let inner = CGRect(x: cx - 4, y: cy - 4, width: 8, height: 8)
                        ctx.fill(Path(ellipseIn: outer), with: .color(theme.elevatedCard))
                        ctx.fill(Path(ellipseIn: inner), with: .color(theme.accentCobalt))
                    }

                    // 8. Interactive DragGesture Crosshair
                    if let active = draggedPoint {
                        let cx = mapX(active.x)
                        let cy = mapY(active.y)

                        var vLine = Path()
                        vLine.move(to: CGPoint(x: cx, y: plotRect.minY))
                        vLine.addLine(to: CGPoint(x: cx, y: plotRect.maxY))
                        ctx.stroke(vLine, with: .color(theme.accentCobalt.opacity(0.55)), lineWidth: 1.5)

                        if yr.min <= active.y && active.y <= yr.max {
                            var hLine = Path()
                            hLine.move(to: CGPoint(x: plotRect.minX, y: cy))
                            hLine.addLine(to: CGPoint(x: plotRect.maxX, y: cy))
                            ctx.stroke(hLine, with: .color(theme.accentCobalt.opacity(0.35)), style: StrokeStyle(lineWidth: 1, dash: [4, 4]))

                            let ring = CGRect(x: cx - 8, y: cy - 8, width: 16, height: 16)
                            let dot = CGRect(x: cx - 5, y: cy - 5, width: 10, height: 10)
                            ctx.fill(Path(ellipseIn: ring), with: .color(theme.elevatedCard))
                            ctx.stroke(Path(ellipseIn: ring), with: .color(theme.accentCobalt), lineWidth: 2)
                            ctx.fill(Path(ellipseIn: dot), with: .color(theme.accentCobalt))
                        }
                    }
                }
                .contentShape(Rectangle())
                .gesture(
                    DragGesture(minimumDistance: 0)
                        .onChanged { value in
                            guard !pts.isEmpty else { return }
                            let clampedX = min(max(value.location.x, plotRect.minX), plotRect.maxX)
                            let frac = Double((clampedX - plotRect.minX) / max(1, plotRect.width))
                            let targetX = xr.min + frac * (xr.max - xr.min)
                            if let nearest = pts.min(by: { abs($0.0 - targetX) < abs($1.0 - targetX) }) {
                                draggedPoint = (nearest.0, nearest.1)
                            }
                        }
                        .onEnded { _ in
                            draggedPoint = nil
                        }
                )

                // Top-left HUD readout (live crosshair OR f_N(0) legend)
                HStack(spacing: 8) {
                    if let active = draggedPoint {
                        Text("x = \(formatReadout(active.x))   f_\(currentN)(x) = \(formatReadout(active.y))")
                            .font(.system(size: 15, weight: .bold, design: .monospaced))
                            .monospacedDigit()
                            .foregroundStyle(.white)
                            .padding(.horizontal, 12)
                            .padding(.vertical, 5)
                            .background(theme.accentCobalt, in: Capsule())
                    } else if let p0 = pointAtZero {
                        Text("f_\(currentN)(0) = \(formatReadout(p0.1))  ·  drag to inspect")
                            .font(.system(size: 14, weight: .semibold, design: .monospaced))
                            .foregroundStyle(theme.secondaryInk)
                            .padding(.horizontal, 10)
                            .padding(.vertical, 4)
                            .background(theme.paperBackground.opacity(0.92), in: Capsule())
                            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                    } else {
                        Text("N = \(currentN)  ·  drag curve to inspect")
                            .font(.system(size: 14, weight: .semibold, design: .monospaced))
                            .foregroundStyle(theme.secondaryInk)
                            .padding(.horizontal, 10)
                            .padding(.vertical, 4)
                            .background(theme.paperBackground.opacity(0.92), in: Capsule())
                            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                    }
                }
                .padding(.leading, insetLeft + 8)
                .padding(.top, insetTop + 4)
                .allowsHitTesting(false)
            }
        }
    }

    // MARK: - Exact Lean 4 FastLC Probes Strip

    private func probesSection(_ probes: [FnProbe]) -> some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                Text("EXACT LEAN 4 FastLC PROBES")
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .tracking(0.8)
                    .foregroundStyle(theme.secondaryInk)
                Spacer()
                if selectedProbe != nil {
                    Button("Clear") { selectedProbe = nil }
                        .font(.system(size: 14, weight: .semibold, design: .rounded))
                        .foregroundStyle(theme.accentCobalt)
                        .buttonStyle(.plain)
                }
            }

            let columns = [
                GridItem(.flexible(), spacing: 8),
                GridItem(.flexible(), spacing: 8),
                GridItem(.flexible(), spacing: 8),
            ]

            LazyVGrid(columns: columns, spacing: 8) {
                ForEach(probes) { probe in
                    let isSelected = selectedProbe?.id == probe.id
                    Button {
                        withAnimation(.easeInOut(duration: 0.15)) {
                            selectedProbe = isSelected ? nil : probe
                        }
                    } label: {
                        VStack(alignment: .leading, spacing: 3) {
                            Text("x = \(probe.x_label)")
                                .font(.system(size: 13, weight: .bold, design: .monospaced))
                                .foregroundStyle(theme.accentCobalt)
                            if probe.ok {
                                Text(probe.exact ?? probe.approx ?? "—")
                                    .font(.system(size: 16, weight: .semibold, design: .monospaced))
                                    .foregroundStyle(theme.primaryInk)
                                    .lineLimit(1)
                                    .truncationMode(.tail)
                            } else {
                                Text("undef")
                                    .font(.system(size: 15, weight: .medium, design: .monospaced))
                                    .foregroundStyle(theme.errorRed)
                            }
                        }
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 8)
                        .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                        .overlay(
                            RoundedRectangle(cornerRadius: 10, style: .continuous)
                                .stroke(isSelected ? theme.accentCobalt : theme.borderSubtle, lineWidth: isSelected ? 2 : 1)
                        )
                    }
                    .buttonStyle(.plain)
                }
            }

            if let probe = selectedProbe {
                VStack(alignment: .leading, spacing: 4) {
                    Text("f(\(probe.x_label))  ·  \((probe.regime ?? "value").uppercased())")
                        .font(.system(size: 13, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                    Text(probe.ok ? (probe.exact ?? probe.approx ?? "—") : (probe.error ?? "Undefined"))
                        .font(.system(size: 17, weight: .semibold, design: .monospaced))
                        .foregroundStyle(probe.ok ? theme.primaryInk : theme.errorRed)
                        .textSelection(.enabled)
                }
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(10)
                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.accentCobalt.opacity(0.45), lineWidth: 1))
            }
        }
    }

    private func formatAxisTick(_ val: Double) -> String {
        if abs(val) < 1e-9 { return "0" }
        if abs(val - val.rounded()) < 1e-4 && abs(val) < 10_000 {
            return String(format: "%.0f", val.rounded())
        }
        if abs(val) >= 1000 || abs(val) < 0.01 {
            return String(format: "%.1e", val)
        }
        return String(format: "%.2g", val)
    }

    private func formatReadout(_ val: Double) -> String {
        if abs(val) < 1e-9 { return "0" }
        if abs(val) >= 1e5 || abs(val) < 1e-4 {
            return String(format: "%.4e", val)
        }
        return String(format: "%.4f", val)
    }
}
