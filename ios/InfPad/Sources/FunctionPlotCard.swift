import SwiftUI

enum PlotZoomMode: String, CaseIterable, Identifiable {
    case macro
    case micro
    var id: String { rawValue }
}

enum PlotScaleMode: String, CaseIterable, Identifiable {
    case auto = "Auto"
    case linear = "Lin"
    case symlogY = "SymLog Y"
    case logLog = "Log-Log"
    var id: String { rawValue }
}

// MARK: - Generic 1D Function Plot Card (`kind == "fn"`) with Auto | Lin | SymLog Y | Log-Log

struct FunctionPlotCard: View {
    let eval: EvalResponse
    let plot: FnPlot
    let theme: InfTheme
    let currentN: Int
    let latencyText: String?

    @State private var zoomMode: PlotZoomMode = .macro
    @State private var scaleMode: PlotScaleMode = .auto
    @State private var draggedPoint: (x: Double, y: Double)? = nil
    @State private var selectedProbe: FnProbe? = nil

    private var varName: String { eval.effectiveVarName }

    private var rawPoints: [(Double, Double)] {
        let source: [[Double]]
        if zoomMode == .micro, let zp = plot.zoom_points, !zp.isEmpty {
            source = zp
        } else {
            source = plot.points ?? []
        }
        return source.compactMap { pair in
            guard pair.count >= 2, pair[0].isFinite, pair[1].isFinite else { return nil }
            return (pair[0], pair[1])
        }
    }

    private var effectiveScale: PlotScaleMode {
        if scaleMode != .auto { return scaleMode }
        switch (eval.effectiveScaleHint ?? "").lowercased() {
        case "loglog": return .logLog
        case "symlog": return .symlogY
        case "linear": return .linear
        default:
            return Self.inferScale(points: rawPoints)
        }
    }

    private static func inferScale(points: [(Double, Double)]) -> PlotScaleMode {
        let absYs = points.map { abs($0.1) }.filter { $0 > 0 }.sorted()
        guard let maxY = absYs.last else { return .linear }
        let medY = absYs[absYs.count / 2]
        let allPos = points.allSatisfy { $0.1 > 0 }
        let posXs = points.map { $0.0 }.filter { $0 > 0 }
        if allPos, let minPosY = absYs.first, maxY / max(minPosY, 1e-15) >= 1000.0 {
            if let minX = posXs.min(), let maxX = posXs.max(), maxX / max(minX, 1e-15) >= 100.0 {
                return .logLog
            }
            return .symlogY
        }
        if maxY / max(medY, 1e-6) >= 1000.0 {
            return .symlogY
        }
        return .linear
    }

    private var linthresh: Double {
        let posYs = rawPoints.map { abs($0.1) }.filter { $0 > 1e-9 }.sorted()
        guard !posYs.isEmpty else { return 1.0 }
        let p25 = posYs[posYs.count / 4]
        return max(1e-6, min(1.0, p25))
    }

    private func symLog(_ y: Double) -> Double {
        let t = linthresh
        let s: Double = y < 0 ? -1.0 : (y > 0 ? 1.0 : 0.0)
        return s * log10(1.0 + abs(y) / t)
    }

    private var displayPoints: [(rawX: Double, rawY: Double, tx: Double, ty: Double)] {
        switch effectiveScale {
        case .linear, .auto:
            return rawPoints.map { ($0.0, $0.1, $0.0, $0.1) }
        case .symlogY:
            return rawPoints.map { ($0.0, $0.1, $0.0, symLog($0.1)) }
        case .logLog:
            return rawPoints.compactMap { p in
                guard p.0 > 0 && p.1 > 0 else { return nil }
                return (p.0, p.1, log10(p.0), log10(p.1))
            }
        }
    }

    private var xRange: (min: Double, max: Double) {
        if effectiveScale == .logLog {
            let txs = displayPoints.map { $0.tx }
            guard let lo = txs.min(), let hi = txs.max() else { return (-2, 0) }
            if abs(hi - lo) < 1e-9 { return (lo - 1, hi + 1) }
            return (lo, hi)
        }
        if zoomMode == .micro, let x0 = plot.zoom_x_min, let x1 = plot.zoom_x_max, x1 > x0 {
            return (x0, x1)
        }
        let lo = plot.x_min ?? -1.0
        let hi = (plot.x_max ?? 1.0) > lo ? (plot.x_max ?? 1.0) : lo + 2.0
        return (lo, hi)
    }

    private var yRange: (min: Double, max: Double) {
        let rawMin: Double
        let rawMax: Double
        switch effectiveScale {
        case .linear, .auto:
            if zoomMode == .micro, let y0 = plot.zoom_y_min, let y1 = plot.zoom_y_max {
                rawMin = y0; rawMax = y1
            } else {
                rawMin = plot.y_min ?? -1.0; rawMax = plot.y_max ?? 1.0
            }
        case .symlogY:
            let tys = displayPoints.map { $0.ty }
            rawMin = tys.min() ?? -1.0
            rawMax = tys.max() ?? 1.0
        case .logLog:
            let tys = displayPoints.map { $0.ty }
            rawMin = tys.min() ?? -1.0
            rawMax = tys.max() ?? 1.0
        }
        let span = rawMax - rawMin
        if span < 1e-9 { return (rawMin - 1.0, rawMax + 1.0) }
        let pad = span * 0.07
        return (rawMin - pad, rawMax + pad)
    }

    private var pointAtZero: (Double, Double)? {
        guard effectiveScale != .logLog else { return nil }
        guard !rawPoints.isEmpty else { return nil }
        guard let closest = rawPoints.min(by: { abs($0.0) < abs($1.0) }) else { return nil }
        let tol = max(1e-9, (xRange.max - xRange.min) * 1e-4)
        return abs(closest.0) <= tol ? closest : nil
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            // Header row: Badge + Latency + Zoom pills
            HStack(spacing: 8) {
                let style = theme.regimeStyle(eval.regime)
                Text("FUNCTION f(\(varName))")
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .foregroundStyle(style.fg)
                    .padding(.horizontal, 10)
                    .padding(.vertical, 5)
                    .background(style.bg, in: Capsule())

                if let latencyText {
                    Text(latencyText)
                        .font(.system(size: 14, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 4)
                        .background(theme.elevatedCard, in: Capsule())
                        .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                }

                Spacer(minLength: 4)

                if plot.hasZoom {
                    HStack(spacing: 3) {
                        zoomPill(mode: .macro, label: "Macro [-1, 1]")
                        zoomPill(mode: .micro, label: "Micro ±8ε")
                    }
                    .padding(3)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }
            }

            // Adaptive Axis Scale Pill Row
            ScaleSelectorRow(scaleMode: $scaleMode, effectiveScale: effectiveScale, theme: theme)

            // Plot Canvas (or graceful Log-Log empty note)
            if effectiveScale == .logLog && displayPoints.count < 2 {
                VStack(spacing: 8) {
                    Image(systemName: "chart.xyaxis.line")
                        .font(.system(size: 28))
                        .foregroundStyle(theme.secondaryInk)
                    Text("No positive (\(varName) > 0, y > 0) points for Log-Log scale. Switch to Auto or SymLog Y.")
                        .font(.system(size: 16, weight: .medium, design: .rounded))
                        .foregroundStyle(theme.secondaryInk)
                        .multilineTextAlignment(.center)
                }
                .frame(maxWidth: .infinity)
                .frame(height: 220)
                .padding(16)
                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 16, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 16, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1.25))
            } else {
                plotCanvasView
                    .frame(height: 220)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 16, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 16, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1.25))
            }

            // Compact Exact Lean 4 FastLC Probes Strip
            if let probes = eval.probes, !probes.isEmpty {
                ProbeGridSection(probes: probes, varName: varName, theme: theme, selectedProbe: $selectedProbe)
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
        .onChange(of: eval.input) { _, _ in
            draggedPoint = nil
            selectedProbe = nil
            scaleMode = .auto
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
                .font(.system(size: 14, weight: .bold, design: .rounded))
                .foregroundStyle(active ? .white : theme.primaryInk)
                .padding(.horizontal, 10)
                .padding(.vertical, 5)
                .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 8, style: .continuous))
        }
        .buttonStyle(.plain)
    }

    private var plotCanvasView: some View {
        GeometryReader { geo in
            let insetLeft: CGFloat = 64
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
            let pts = displayPoints
            let activeScale = effectiveScale

            ZStack(alignment: .topLeading) {
                Canvas { ctx, _ in
                    func mapX(_ tx: Double) -> CGFloat {
                        let t = (tx - xr.min) / max(1e-12, xr.max - xr.min)
                        return plotRect.minX + CGFloat(t) * plotRect.width
                    }

                    func mapY(_ ty: Double) -> CGFloat {
                        let t = (ty - yr.min) / max(1e-12, yr.max - yr.min)
                        return plotRect.maxY - CGFloat(t) * plotRect.height
                    }

                    // 1. Horizontal gridlines & Y ticks
                    let yTickSpecs: [(Double, String)] = {
                        switch activeScale {
                        case .logLog:
                            let eMin = Int(ceil(yr.min))
                            let eMax = Int(floor(yr.max))
                            if eMax >= eMin {
                                let step = max(1, (eMax - eMin) / 3)
                                return stride(from: eMin, through: eMax, by: step).map { (Double($0), MathUnicode.powerOfTen($0)) }
                            }
                            return [(yr.min, MathUnicode.formatTick(pow(10, yr.min))), (yr.max, MathUnicode.formatTick(pow(10, yr.max)))]
                        case .symlogY:
                            let lo = rawPoints.map { $0.1 }.min() ?? -1
                            let hi = rawPoints.map { $0.1 }.max() ?? 1
                            var ticks: [(Double, String)] = []
                            if lo < 0 { ticks.append((symLog(lo), MathUnicode.formatTick(lo))) }
                            if lo <= 0 && hi >= 0 { ticks.append((0.0, "0")) }
                            if hi > 0 { ticks.append((symLog(hi), MathUnicode.formatTick(hi))) }
                            return ticks.isEmpty ? [(0.0, "0")] : ticks
                        case .linear, .auto:
                            let y0 = (zoomMode == .micro ? plot.zoom_y_min : plot.y_min) ?? yr.min
                            let y1 = (zoomMode == .micro ? plot.zoom_y_max : plot.y_max) ?? yr.max
                            let ym = (y0 + y1) / 2.0
                            let vals = abs(y1 - y0) < 1e-9 ? [y0] : [y0, ym, y1]
                            return vals.map { ($0, MathUnicode.formatTick($0)) }
                        }
                    }()

                    for (tyVal, labelStr) in yTickSpecs {
                        let py = mapY(tyVal)
                        guard py >= plotRect.minY - 6 && py <= plotRect.maxY + 6 else { continue }
                        var gridPath = Path()
                        gridPath.move(to: CGPoint(x: plotRect.minX, y: py))
                        gridPath.addLine(to: CGPoint(x: plotRect.maxX, y: py))
                        ctx.stroke(gridPath, with: .color(theme.borderSubtle), lineWidth: 1)

                        let label = Text(labelStr)
                            .font(.system(size: 13, weight: .medium, design: .monospaced))
                            .foregroundColor(theme.secondaryInk)
                        ctx.draw(label, at: CGPoint(x: plotRect.minX - 8, y: py), anchor: .trailing)
                    }

                    // 2. X baseline (y = 0 if visible in linear/symlog)
                    if activeScale != .logLog && yr.min <= 0 && yr.max >= 0 {
                        let y0 = mapY(0)
                        var base = Path()
                        base.move(to: CGPoint(x: plotRect.minX, y: y0))
                        base.addLine(to: CGPoint(x: plotRect.maxX, y: y0))
                        ctx.stroke(base, with: .color(theme.secondaryInk.opacity(0.32)), lineWidth: 1)
                    }

                    // 3. Dashed vertical guide at x = 0
                    if activeScale != .logLog && xr.min <= 0 && xr.max >= 0 {
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

                    // 4. Axes border
                    var axes = Path()
                    axes.move(to: CGPoint(x: plotRect.minX, y: plotRect.minY))
                    axes.addLine(to: CGPoint(x: plotRect.minX, y: plotRect.maxY))
                    axes.addLine(to: CGPoint(x: plotRect.maxX, y: plotRect.maxY))
                    ctx.stroke(axes, with: .color(theme.secondaryInk.opacity(0.42)), lineWidth: 1.25)

                    // 5. X ticks
                    let xLabels: [(Double, String)] = {
                        if activeScale == .logLog {
                            let eMin = Int(ceil(xr.min))
                            let eMax = Int(floor(xr.max))
                            if eMax >= eMin {
                                let step = max(1, (eMax - eMin) / 3)
                                return stride(from: eMin, through: eMax, by: step).map { (Double($0), MathUnicode.powerOfTen($0)) }
                            }
                            return [(xr.min, MathUnicode.formatTick(pow(10, xr.min))), (xr.max, MathUnicode.formatTick(pow(10, xr.max)))]
                        }
                        if zoomMode == .micro {
                            return [(xr.min, "-8ε"), (0.0, "0"), (xr.max, "+8ε")]
                        }
                        return [(xr.min, MathUnicode.formatTick(xr.min)), (0.0, "0"), (xr.max, MathUnicode.formatTick(xr.max))]
                    }()
                    for (xv, lbl) in xLabels {
                        let px = mapX(xv)
                        let tickText = Text(lbl)
                            .font(.system(size: 13, weight: .semibold, design: .monospaced))
                            .foregroundColor(theme.secondaryInk)
                        ctx.draw(tickText, at: CGPoint(x: px, y: plotRect.maxY + 15), anchor: .center)
                    }

                    // 6. Clipped continuous segments + discontinuity-safe fill + 2.8pt curve
                    if pts.count >= 2 {
                        let maxJump = plotRect.height * 0.65
                        var segments: [[CGPoint]] = []
                        var currentSeg: [CGPoint] = []
                        var prevTy: Double? = nil
                        let ySpan = max(1e-9, yr.max - yr.min)

                        for p in pts {
                            let px = mapX(p.tx)
                            let py = mapY(p.ty)
                            let isPoleSignFlip = (prevTy != nil) && (
                                (prevTy! < yr.min && p.ty > yr.max) ||
                                (prevTy! > yr.max && p.ty < yr.min) ||
                                (activeScale != .logLog && prevTy! * p.ty < 0 && abs(p.ty - prevTy!) > 0.55 * ySpan)
                            )
                            if let lastPt = currentSeg.last, (abs(py - lastPt.y) > maxJump || isPoleSignFlip) {
                                if !currentSeg.isEmpty { segments.append(currentSeg) }
                                currentSeg = [CGPoint(x: px, y: py)]
                            } else {
                                currentSeg.append(CGPoint(x: px, y: py))
                            }
                            prevTy = p.ty
                        }
                        if !currentSeg.isEmpty { segments.append(currentSeg) }

                        var clipped = ctx
                        clipped.clip(to: Path(plotRect))

                        if segments.count == 1, let seg = segments.first, seg.count >= 2 {
                            let baselineY = (activeScale != .logLog && yr.min <= 0 && yr.max >= 0) ? mapY(0) : plotRect.maxY
                            var fillPath = Path()
                            fillPath.move(to: seg[0])
                            for pt in seg.dropFirst() { fillPath.addLine(to: pt) }
                            fillPath.addLine(to: CGPoint(x: seg.last!.x, y: baselineY))
                            fillPath.addLine(to: CGPoint(x: seg.first!.x, y: baselineY))
                            fillPath.closeSubpath()
                            clipped.fill(fillPath, with: .color(theme.accentCobalt.opacity(0.08)))
                        }

                        var curve = Path()
                        for seg in segments where seg.count >= 2 {
                            curve.move(to: seg[0])
                            for pt in seg.dropFirst() { curve.addLine(to: pt) }
                        }
                        clipped.stroke(
                            curve,
                            with: .color(theme.accentCobalt),
                            style: StrokeStyle(lineWidth: 2.8, lineCap: .round, lineJoin: .round)
                        )
                    }

                    // 7. Highlighted dot at (0, fₙ(0)) when x = 0 is sampled & in-frame
                    if let p0 = pointAtZero {
                        let ty0 = activeScale == .symlogY ? symLog(p0.1) : p0.1
                        if xr.min <= p0.0 && p0.0 <= xr.max && yr.min <= ty0 && ty0 <= yr.max {
                            let cx = mapX(p0.0)
                            let cy = mapY(ty0)
                            let outer = CGRect(x: cx - 6, y: cy - 6, width: 12, height: 12)
                            let inner = CGRect(x: cx - 4, y: cy - 4, width: 8, height: 8)
                            ctx.fill(Path(ellipseIn: outer), with: .color(theme.elevatedCard))
                            ctx.fill(Path(ellipseIn: inner), with: .color(theme.accentCobalt))
                        }
                    }

                    // 8. Interactive DragGesture Crosshair
                    if let active = draggedPoint {
                        let tx = activeScale == .logLog ? log10(max(1e-15, active.x)) : active.x
                        let ty: Double = {
                            switch activeScale {
                            case .logLog: return log10(max(1e-15, active.y))
                            case .symlogY: return symLog(active.y)
                            case .linear, .auto: return active.y
                            }
                        }()
                        let cx = mapX(tx)
                        let cy = mapY(ty)

                        var vLine = Path()
                        vLine.move(to: CGPoint(x: cx, y: plotRect.minY))
                        vLine.addLine(to: CGPoint(x: cx, y: plotRect.maxY))
                        ctx.stroke(vLine, with: .color(theme.accentCobalt.opacity(0.55)), lineWidth: 1.5)

                        if yr.min <= ty && ty <= yr.max {
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
                            let targetTx = xr.min + frac * (xr.max - xr.min)
                            if let nearest = pts.min(by: { abs($0.tx - targetTx) < abs($1.tx - targetTx) }) {
                                draggedPoint = (nearest.rawX, nearest.rawY)
                            }
                        }
                        .onEnded { _ in
                            draggedPoint = nil
                        }
                )

                // Top-left HUD readout with clean Unicode subscript f₁₀₀(0)
                HStack(spacing: 8) {
                    if let active = draggedPoint {
                        Text("\(varName) = \(MathUnicode.formatReadout(active.x))   \(MathUnicode.fnSubscript(currentN, arg: varName)) = \(MathUnicode.formatReadout(active.y))")
                            .font(.system(size: 14, weight: .bold, design: .monospaced))
                            .monospacedDigit()
                            .foregroundStyle(.white)
                            .padding(.horizontal, 12)
                            .padding(.vertical, 5)
                            .background(theme.accentCobalt, in: Capsule())
                    } else if let p0 = pointAtZero {
                        Text("\(MathUnicode.fnSubscript(currentN, arg: "0")) = \(MathUnicode.formatReadout(p0.1))  ·  drag to inspect")
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
}

// MARK: - Constant Finite-Projection Scaling Curve Card (`kind == "num"`, `plot_decision == "finite_projection"`)

struct ConstantScalePlotCard: View {
    let eval: EvalResponse
    let plot: FnPlot
    let theme: InfTheme
    let currentN: Int

    @State private var scaleMode: PlotScaleMode = .auto
    @State private var draggedPoint: (n: Double, y: Double)? = nil

    private var rawPoints: [(Double, Double)] {
        (plot.scale_curve ?? []).compactMap { pair in
            guard pair.count >= 2, pair[0].isFinite, pair[1].isFinite else { return nil }
            return (pair[0], pair[1])
        }
    }

    private var effectiveScale: PlotScaleMode {
        if scaleMode != .auto { return scaleMode }
        switch (eval.effectiveScaleHint ?? "").lowercased() {
        case "loglog": return .logLog
        case "symlog": return .symlogY
        case "linear": return .linear
        default:
            let absYs = rawPoints.map { abs($0.1) }.filter { $0 > 0 }
            if let lo = absYs.min(), let hi = absYs.max(), hi / max(lo, 1e-15) >= 1000.0 {
                return rawPoints.allSatisfy({ $0.1 > 0 }) ? .logLog : .symlogY
            }
            return .linear
        }
    }

    private var linthresh: Double {
        let posYs = rawPoints.map { abs($0.1) }.filter { $0 > 1e-9 }.sorted()
        guard !posYs.isEmpty else { return 1.0 }
        return max(1e-6, min(1.0, posYs[posYs.count / 4]))
    }

    private func symLog(_ y: Double) -> Double {
        let s: Double = y < 0 ? -1.0 : (y > 0 ? 1.0 : 0.0)
        return s * log10(1.0 + abs(y) / linthresh)
    }

    private var displayPoints: [(rawN: Double, rawY: Double, tx: Double, ty: Double)] {
        switch effectiveScale {
        case .linear, .auto:
            return rawPoints.map { ($0.0, $0.1, $0.0, $0.1) }
        case .symlogY:
            return rawPoints.map { ($0.0, $0.1, $0.0, symLog($0.1)) }
        case .logLog:
            return rawPoints.compactMap { p in
                guard p.0 > 0 && p.1 > 0 else { return nil }
                return (p.0, p.1, log10(p.0), log10(p.1))
            }
        }
    }

    private var currentMarker: (n: Double, y: Double)? {
        let nD = Double(currentN)
        if let fy = eval.localEvalFinite(at: nD) ?? plot.finite_y ?? eval.eval_finite, fy.isFinite {
            return (nD, fy)
        }
        return rawPoints.min(by: { abs($0.0 - nD) < abs($1.0 - nD) })
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Text("SCALING CURVE  H ↦ N")
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .tracking(0.8)
                    .foregroundStyle(theme.secondaryInk)
                Spacer()
                if let m = draggedPoint ?? currentMarker {
                    Text("N = \(Int(m.n.rounded()))  ->  \(MathUnicode.formatReadout(m.y))")
                        .font(.system(size: 14, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                }
            }

            ScaleSelectorRow(scaleMode: $scaleMode, effectiveScale: effectiveScale, theme: theme)

            if effectiveScale == .logLog && displayPoints.count < 2 {
                Text("No positive scaling points for Log-Log scale. Switch to Auto or SymLog Y.")
                    .font(.system(size: 15, design: .rounded))
                    .foregroundStyle(theme.secondaryInk)
                    .frame(maxWidth: .infinity)
                    .frame(height: 170)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
            } else {
                GeometryReader { geo in
                    let insetLeft: CGFloat = 64
                    let insetRight: CGFloat = 20
                    let insetTop: CGFloat = 16
                    let insetBottom: CGFloat = 30
                    let plotRect = CGRect(
                        x: insetLeft, y: insetTop,
                        width: max(40, geo.size.width - insetLeft - insetRight),
                        height: max(40, geo.size.height - insetTop - insetBottom)
                    )
                    let pts = displayPoints
                    let txs = pts.map { $0.tx }
                    let tys = pts.map { $0.ty }
                    let xLo = txs.min() ?? 0
                    let xHi = max(xLo + 1e-6, txs.max() ?? 1)
                    let rawYLo = tys.min() ?? -1
                    let rawYHi = tys.max() ?? 1
                    let ySpan = abs(rawYHi - rawYLo) < 1e-9 ? 2.0 : (rawYHi - rawYLo)
                    let yLo = abs(rawYHi - rawYLo) < 1e-9 ? rawYLo - 1.0 : rawYLo - ySpan * 0.08
                    let yHi = abs(rawYHi - rawYLo) < 1e-9 ? rawYHi + 1.0 : rawYHi + ySpan * 0.08
                    let activeScale = effectiveScale

                    Canvas { ctx, _ in
                        func mapX(_ tx: Double) -> CGFloat {
                            plotRect.minX + CGFloat((tx - xLo) / max(1e-12, xHi - xLo)) * plotRect.width
                        }
                        func mapY(_ ty: Double) -> CGFloat {
                            plotRect.maxY - CGFloat((ty - yLo) / max(1e-12, yHi - yLo)) * plotRect.height
                        }

                        // Y ticks
                        let yTicks: [(Double, String)] = activeScale == .logLog
                            ? [(rawYLo, MathUnicode.formatTick(pow(10, rawYLo))), (rawYHi, MathUnicode.formatTick(pow(10, rawYHi)))]
                            : [
                                (rawYLo, MathUnicode.formatTick(rawPoints.map { $0.1 }.min() ?? rawYLo)),
                                (rawYHi, MathUnicode.formatTick(rawPoints.map { $0.1 }.max() ?? rawYHi)),
                              ]
                        for (ty, lbl) in yTicks {
                            let py = mapY(ty)
                            var g = Path()
                            g.move(to: CGPoint(x: plotRect.minX, y: py))
                            g.addLine(to: CGPoint(x: plotRect.maxX, y: py))
                            ctx.stroke(g, with: .color(theme.borderSubtle), lineWidth: 1)
                            ctx.draw(Text(lbl).font(.system(size: 12, weight: .medium, design: .monospaced)).foregroundColor(theme.secondaryInk), at: CGPoint(x: plotRect.minX - 8, y: py), anchor: .trailing)
                        }

                        // Axes
                        var axes = Path()
                        axes.move(to: CGPoint(x: plotRect.minX, y: plotRect.minY))
                        axes.addLine(to: CGPoint(x: plotRect.minX, y: plotRect.maxY))
                        axes.addLine(to: CGPoint(x: plotRect.maxX, y: plotRect.maxY))
                        ctx.stroke(axes, with: .color(theme.secondaryInk.opacity(0.4)), lineWidth: 1.2)

                        // X ticks (N)
                        let xLabels: [(Double, String)] = activeScale == .logLog
                            ? [(xLo, MathUnicode.powerOfTen(Int(xLo.rounded()))), (xHi, MathUnicode.powerOfTen(Int(xHi.rounded())))]
                            : [(xLo, "N=\(Int(xLo.rounded()))"), (xHi, "N=\(Int(xHi.rounded()))")]
                        for (tx, lbl) in xLabels {
                            ctx.draw(Text(lbl).font(.system(size: 12, weight: .semibold, design: .monospaced)).foregroundColor(theme.secondaryInk), at: CGPoint(x: mapX(tx), y: plotRect.maxY + 14), anchor: .center)
                        }

                        // Curve
                        if pts.count >= 2 {
                            var curve = Path()
                            for (idx, p) in pts.enumerated() {
                                let pt = CGPoint(x: mapX(p.tx), y: mapY(p.ty))
                                if idx == 0 { curve.move(to: pt) } else { curve.addLine(to: pt) }
                            }
                            ctx.stroke(curve, with: .color(theme.accentCobalt), style: StrokeStyle(lineWidth: 2.6, lineCap: .round, lineJoin: .round))
                        }

                        // Highlight dot at current H ↦ N
                        if let m = draggedPoint ?? currentMarker {
                            let okLog = activeScale != .logLog || (m.n > 0 && m.y > 0)
                            if okLog {
                                let tx = activeScale == .logLog ? log10(m.n) : m.n
                                let ty: Double = activeScale == .logLog ? log10(m.y) : (activeScale == .symlogY ? symLog(m.y) : m.y)
                                if tx >= xLo && tx <= xHi && ty >= yLo && ty <= yHi {
                                    let cx = mapX(tx), cy = mapY(ty)
                                    let ring = CGRect(x: cx - 7, y: cy - 7, width: 14, height: 14)
                                    let dot = CGRect(x: cx - 4.5, y: cy - 4.5, width: 9, height: 9)
                                    ctx.fill(Path(ellipseIn: ring), with: .color(theme.elevatedCard))
                                    ctx.stroke(Path(ellipseIn: ring), with: .color(theme.accentCobalt), lineWidth: 2)
                                    ctx.fill(Path(ellipseIn: dot), with: .color(theme.accentCobalt))
                                }
                            }
                        }
                    }
                    .contentShape(Rectangle())
                    .gesture(
                        DragGesture(minimumDistance: 0)
                            .onChanged { val in
                                guard !pts.isEmpty else { return }
                                let cx = min(max(val.location.x, plotRect.minX), plotRect.maxX)
                                let frac = Double((cx - plotRect.minX) / max(1, plotRect.width))
                                let targetTx = xLo + frac * (xHi - xLo)
                                if let nearest = pts.min(by: { abs($0.tx - targetTx) < abs($1.tx - targetTx) }) {
                                    draggedPoint = (nearest.rawN, nearest.rawY)
                                }
                            }
                            .onEnded { _ in draggedPoint = nil }
                    )
                }
                .frame(height: 170)
                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }
}

// MARK: - 2-Var (`fn2`) & 3-Var (`fn3`) Heatmap Plot Card

struct HeatmapPlotCard: View {
    let eval: EvalResponse
    let theme: InfTheme
    let currentN: Int
    let latencyText: String?

    @State private var sliceIndex: Int = 4 // defaults to z = 0 slice (middle of 9 slices)
    @State private var inspectedCell: (x: Double, y: Double, val: Double?)? = nil
    @State private var selectedProbe: FnProbe? = nil

    private var gridSize: Int { max(1, eval.effectiveGridSize) }
    private var varNames: [String] { eval.effectiveVars }
    private var is3D: Bool { eval.kind == "fn3" && !(eval.effectiveSlices?.isEmpty ?? true) }

    private var activeGrid: [Double?] {
        if is3D, let slices = eval.effectiveSlices, !slices.isEmpty {
            let clamped = max(0, min(slices.count - 1, sliceIndex))
            return slices[clamped]
        }
        return eval.effectiveValues ?? []
    }

    private var currentSliceZ: Double? {
        guard is3D, let sv = eval.effectiveSliceValues, !sv.isEmpty else { return nil }
        return sv[max(0, min(sv.count - 1, sliceIndex))]
    }

    /// Astigmatism-friendly Cobalt -> Warm Paper -> Warm Amber colormap.
    private func heatmapColor(value: Double?, zMin: Double, zMax: Double) -> Color {
        guard let v = value, v.isFinite else {
            return theme.secondaryInk.opacity(0.22)
        }
        let span = max(1e-9, zMax - zMin)
        let t = max(0.0, min(1.0, (v - zMin) / span))
        if t < 0.5 {
            let u = t * 2.0
            // Cobalt (#1d4ed8) -> Warm Paper (#f4f1e6)
            let r = 0.114 + (0.957 - 0.114) * u
            let g = 0.306 + (0.945 - 0.306) * u
            let b = 0.847 + (0.902 - 0.847) * u
            return Color(red: r, green: g, blue: b)
        } else {
            let u = (t - 0.5) * 2.0
            // Warm Paper (#f4f1e6) -> Warm Amber/Vermilion (#c2410c)
            let r = 0.957 + (0.761 - 0.957) * u
            let g = 0.945 + (0.255 - 0.945) * u
            let b = 0.902 + (0.047 - 0.902) * u
            return Color(red: r, green: g, blue: b)
        }
    }

    var body: some View {
        let zRange = eval.effectiveZRange
        let axes = eval.effectiveAxisRanges
        let v0 = varNames.first ?? "x"
        let v1 = varNames.count > 1 ? varNames[1] : "y"
        let v2 = varNames.count > 2 ? varNames[2] : "z"

        VStack(alignment: .leading, spacing: 12) {
            HStack(spacing: 8) {
                let style = theme.regimeStyle("function")
                Text("HEATMAP f(\(varNames.joined(separator: ", ")))")
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .foregroundStyle(style.fg)
                    .padding(.horizontal, 10)
                    .padding(.vertical, 5)
                    .background(style.bg, in: Capsule())

                if let latencyText {
                    Text(latencyText)
                        .font(.system(size: 14, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 4)
                        .background(theme.elevatedCard, in: Capsule())
                        .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                }

                Spacer()

                if let cell = inspectedCell {
                    let valStr = cell.val.map { MathUnicode.formatReadout($0) } ?? "pole"
                    Text("(\(MathUnicode.formatTick(cell.x)), \(MathUnicode.formatTick(cell.y))) -> \(valStr)")
                        .font(.system(size: 14, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                }
            }

            // Heatmap Canvas + Colorbar
            HStack(spacing: 12) {
                GeometryReader { geo in
                    let insetLeft: CGFloat = 40
                    let insetBottom: CGFloat = 28
                    let insetTop: CGFloat = 10
                    let insetRight: CGFloat = 10
                    let side = min(
                        max(80, geo.size.width - insetLeft - insetRight),
                        max(80, geo.size.height - insetTop - insetBottom)
                    )
                    let originX = insetLeft + (geo.size.width - insetLeft - insetRight - side) / 2
                    let plotRect = CGRect(x: originX, y: insetTop, width: side, height: side)
                    let n = gridSize
                    let grid = activeGrid

                    Canvas { ctx, _ in
                        let cellW = plotRect.width / CGFloat(n)
                        let cellH = plotRect.height / CGFloat(n)

                        for row in 0..<n {
                            for col in 0..<n {
                                let idx = row * n + col
                                let v = idx < grid.count ? grid[idx] : nil
                                // Row 0 is y_min (bottom), Row n-1 is y_max (top)
                                let py = plotRect.maxY - CGFloat(row + 1) * cellH
                                let px = plotRect.minX + CGFloat(col) * cellW
                                let rect = CGRect(x: px, y: py, width: cellW + 0.5, height: cellH + 0.5)
                                ctx.fill(Path(rect), with: .color(heatmapColor(value: v, zMin: zRange.min, zMax: zRange.max)))
                            }
                        }

                        ctx.stroke(Path(plotRect), with: .color(theme.secondaryInk.opacity(0.45)), lineWidth: 1.2)

                        // Axis labels
                        ctx.draw(Text("\(v0) ∈ [\(MathUnicode.formatTick(axes.xMin)), \(MathUnicode.formatTick(axes.xMax))]").font(.system(size: 12, weight: .semibold, design: .monospaced)).foregroundColor(theme.secondaryInk), at: CGPoint(x: plotRect.midX, y: plotRect.maxY + 14))
                        ctx.draw(Text(v1).font(.system(size: 13, weight: .bold, design: .monospaced)).foregroundColor(theme.secondaryInk), at: CGPoint(x: plotRect.minX - 18, y: plotRect.midY))
                    }
                    .contentShape(Rectangle())
                    .gesture(
                        DragGesture(minimumDistance: 0)
                            .onChanged { drag in
                                let nx = max(0, min(0.9999, (drag.location.x - plotRect.minX) / max(1, plotRect.width)))
                                let ny = max(0, min(0.9999, (plotRect.maxY - drag.location.y) / max(1, plotRect.height)))
                                let col = Int(nx * Double(n))
                                let row = Int(ny * Double(n))
                                let idx = row * n + col
                                let val = idx < grid.count ? grid[idx] : nil
                                let xv = axes.xMin + (Double(col) / Double(max(1, n - 1))) * (axes.xMax - axes.xMin)
                                let yv = axes.yMin + (Double(row) / Double(max(1, n - 1))) * (axes.yMax - axes.yMin)
                                inspectedCell = (xv, yv, val)
                            }
                            .onEnded { _ in inspectedCell = nil }
                    )
                }
                .frame(height: 236)

                // Color legend bar
                VStack(spacing: 4) {
                    Text(MathUnicode.formatTick(zRange.max))
                        .font(.system(size: 12, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                    LinearGradient(
                        colors: [
                            Color(red: 0.761, green: 0.255, blue: 0.047),
                            Color(red: 0.957, green: 0.945, blue: 0.902),
                            Color(red: 0.114, green: 0.306, blue: 0.847),
                        ],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                    .frame(width: 18)
                    .clipShape(RoundedRectangle(cornerRadius: 6, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 6, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                    Text(MathUnicode.formatTick(zRange.min))
                        .font(.system(size: 12, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                }
                .frame(height: 210)
            }
            .padding(10)
            .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 16, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 16, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            // 3-var z-slice scrubber
            if is3D, let sv = eval.effectiveSliceValues, sv.count > 1 {
                VStack(alignment: .leading, spacing: 6) {
                    HStack {
                        Text("3D SLICE  \(v2) = \(MathUnicode.formatTick(currentSliceZ ?? 0))")
                            .font(.system(size: 14, weight: .bold, design: .monospaced))
                            .foregroundStyle(theme.accentCobalt)
                        Spacer()
                        Text("Slice \(sliceIndex + 1) / \(sv.count)")
                            .font(.system(size: 13, weight: .medium, design: .monospaced))
                            .foregroundStyle(theme.secondaryInk)
                    }
                    Slider(
                        value: Binding(
                            get: { Double(sliceIndex) },
                            set: { sliceIndex = Int($0.rounded()) }
                        ),
                        in: 0...Double(sv.count - 1),
                        step: 1
                    )
                    .tint(theme.accentCobalt)
                }
                .padding(10)
                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            }

            if let probes = eval.probes, !probes.isEmpty {
                ProbeGridSection(probes: probes, varName: nil, theme: theme, selectedProbe: $selectedProbe)
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
        .onChange(of: eval.input) { _, _ in
            if let sv = eval.effectiveSliceValues, !sv.isEmpty {
                sliceIndex = sv.count / 2
            }
            inspectedCell = nil
            selectedProbe = nil
        }
    }
}

// MARK: - Shared Scale Selector & Exact Probes Grid

private struct ScaleSelectorRow: View {
    @Binding var scaleMode: PlotScaleMode
    let effectiveScale: PlotScaleMode
    let theme: InfTheme

    var body: some View {
        HStack(spacing: 6) {
            Text("SCALE")
                .font(.system(size: 12, weight: .bold, design: .rounded))
                .tracking(0.8)
                .foregroundStyle(theme.secondaryInk)

            HStack(spacing: 3) {
                ForEach(PlotScaleMode.allCases) { mode in
                    let active = scaleMode == mode
                    Button {
                        withAnimation(.easeInOut(duration: 0.14)) { scaleMode = mode }
                    } label: {
                        let caption = (mode == .auto) ? "Auto (\(effectiveScale.rawValue))" : mode.rawValue
                        Text(caption)
                            .font(.system(size: 13, weight: .bold, design: .rounded))
                            .foregroundStyle(active ? .white : theme.primaryInk)
                            .padding(.horizontal, 10)
                            .padding(.vertical, 5)
                            .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 7, style: .continuous))
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(3)
            .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            Spacer()
        }
    }
}

private struct ProbeGridSection: View {
    let probes: [FnProbe]
    let varName: String?
    let theme: InfTheme
    @Binding var selectedProbe: FnProbe?

    var body: some View {
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
                    let headerText = varName != nil && !probe.x_label.hasPrefix("(")
                        ? "\(varName!) = \(probe.x_label)"
                        : probe.x_label
                    Button {
                        withAnimation(.easeInOut(duration: 0.15)) {
                            selectedProbe = isSelected ? nil : probe
                        }
                    } label: {
                        VStack(alignment: .leading, spacing: 3) {
                            Text(headerText)
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
}
