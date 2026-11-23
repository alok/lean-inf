import PencilKit
import SwiftUI

struct ContentView: View {
    @Bindable var store: InfPadStore
    @FocusState private var isExprFocused: Bool
    @State private var copiedFeedback = false
    @State private var hoveredChip: StarterChip? = nil
    @State private var showStarterLegend = false

    private var theme: InfTheme { store.theme }

    var body: some View {
        ZStack {
            theme.paperBackground.ignoresSafeArea()

            VStack(spacing: 0) {
                if !(store.activeTab == .slides && store.isAirPlayClean) {
                    topChromeBar
                }

                if store.activeTab == .slides {
                    SlidesView(store: store)
                } else {
                    calculatorBody
                }
            }

            // Hidden keyboard shortcuts for iPad hardware keyboard / AirPlay presenting
            VStack {
                Button("") { store.activeTab = .calculator }
                    .keyboardShortcut("1", modifiers: .command)
                Button("") { store.activeTab = .slides }
                    .keyboardShortcut("2", modifiers: .command)
                if store.activeTab == .slides {
                    Button("") { store.prevSlide() }
                        .keyboardShortcut(.leftArrow, modifiers: [])
                    Button("") { store.nextSlide() }
                        .keyboardShortcut(.rightArrow, modifiers: [])
                    Button("") { store.nextSlide() }
                        .keyboardShortcut(.space, modifiers: [])
                    Button("") { store.isAirPlayClean.toggle() }
                        .keyboardShortcut("f", modifiers: [])
                }
            }
            .frame(width: 0, height: 0)
            .opacity(0)
            .allowsHitTesting(false)
        }
        .preferredColorScheme(store.isDark ? .dark : .light)
        .sheet(isPresented: $store.showSettings) {
            SettingsSheet(store: store)
        }
        .task {
            await store.bootstrap()
        }
    }

    private var calculatorBody: some View {
        GeometryReader { geo in
            let isLandscape = geo.size.width >= geo.size.height
            if isLandscape {
                HStack(spacing: 16) {
                    leftCanvasPane
                        .frame(width: geo.size.width * 0.54)
                    rightInspectorPane
                        .frame(maxWidth: .infinity)
                }
                .padding(.horizontal, 16)
                .padding(.vertical, 12)
            } else {
                VStack(spacing: 12) {
                    leftCanvasPane
                        .frame(height: geo.size.height * 0.36)
                    rightInspectorPane
                        .frame(maxHeight: .infinity)
                }
                .padding(.horizontal, 16)
                .padding(.vertical, 12)
            }
        }
    }

    // MARK: - Top Header Chrome

    private var topChromeBar: some View {
        HStack(spacing: 14) {
            HStack(spacing: 10) {
                Image(systemName: "infinity.circle.fill")
                    .font(.system(size: 28, weight: .semibold))
                    .foregroundStyle(theme.accentCobalt)
                Text("InfPad")
                    .font(.system(size: 25, weight: .bold, design: .rounded))
                    .foregroundStyle(theme.primaryInk)

                if store.activeTab == .calculator && store.returnedFromSlides {
                    Button {
                        store.returnToSlides()
                    } label: {
                        HStack(spacing: 5) {
                            Image(systemName: "chevron.left")
                                .font(.system(size: 14, weight: .bold))
                            Text("Slides")
                                .font(.system(size: 16, weight: .bold, design: .rounded))
                        }
                        .foregroundStyle(.white)
                        .padding(.horizontal, 12)
                        .padding(.vertical, 6)
                        .background(theme.accentCobalt, in: Capsule())
                    }
                    .buttonStyle(.plain)
                }
            }

            // Clean Calculator | Slides mode switcher
            HStack(spacing: 3) {
                ForEach(InfPadTab.allCases) { tab in
                    let active = store.activeTab == tab
                    Button {
                        store.activeTab = tab
                    } label: {
                        HStack(spacing: 6) {
                            Image(systemName: tab == .calculator ? "function" : "play.rectangle.on.rectangle")
                                .font(.system(size: 15, weight: .bold))
                            Text(tab.rawValue)
                                .font(.system(size: 17, weight: .bold, design: .rounded))
                        }
                        .foregroundStyle(active ? .white : theme.primaryInk)
                        .padding(.horizontal, 14)
                        .padding(.vertical, 7)
                        .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(3)
            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 13, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 13, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            Spacer()

            // Live health status pill
            Button {
                Task { await store.checkHealth() }
            } label: {
                HStack(spacing: 8) {
                    Circle()
                        .fill(store.isConnected ? theme.successGreen : theme.errorRed)
                        .frame(width: 11, height: 11)
                    if let h = store.health, h.ok {
                        Text("Lean \(h.lean ?? "4.36") · \(String(format: "%.1f", h.pingMs ?? 0)) ms")
                            .font(.system(size: 17, weight: .medium, design: .monospaced))
                            .foregroundStyle(theme.primaryInk)
                    } else {
                        Text(store.isCheckingHealth ? "Connecting…" : "Offline · Tap to Retry")
                            .font(.system(size: 17, weight: .medium, design: .rounded))
                            .foregroundStyle(theme.errorRed)
                    }
                }
                .padding(.horizontal, 14)
                .padding(.vertical, 9)
                .background(theme.surfaceCard, in: Capsule())
                .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
            }
            .buttonStyle(.plain)

            // Warm Paper / Soft Slate toggle
            Button {
                store.isDark.toggle()
            } label: {
                Image(systemName: store.isDark ? "sun.max.fill" : "moon.fill")
                    .font(.system(size: 20, weight: .semibold))
                    .foregroundStyle(theme.primaryInk)
                    .frame(width: 44, height: 44)
                    .background(theme.surfaceCard, in: Circle())
                    .overlay(Circle().stroke(theme.borderSubtle, lineWidth: 1))
            }
            .buttonStyle(.plain)
            .accessibilityLabel("Toggle Paper Theme")

            // Settings gear
            Button {
                store.showSettings = true
            } label: {
                Image(systemName: "gearshape.fill")
                    .font(.system(size: 20, weight: .semibold))
                    .foregroundStyle(theme.primaryInk)
                    .frame(width: 44, height: 44)
                    .background(theme.surfaceCard, in: Circle())
                    .overlay(Circle().stroke(theme.borderSubtle, lineWidth: 1))
            }
            .buttonStyle(.plain)
            .accessibilityLabel("Settings")
        }
        .padding(.horizontal, 18)
        .padding(.vertical, 10)
        .background(theme.paperBackground)
        .overlay(alignment: .bottom) {
            Rectangle().fill(theme.borderSubtle).frame(height: 1)
        }
    }

    // MARK: - Left Pane: PencilKit Canvas + Toolbar + Starter Chips

    private var leftCanvasPane: some View {
        VStack(spacing: 12) {
            // Drawing toolbar
            HStack(spacing: 10) {
                // Pencil / Eraser toggle
                HStack(spacing: 4) {
                    toolButton(
                        title: "Pencil",
                        icon: "pencil.tip",
                        active: store.toolMode == .pen
                    ) {
                        store.toolMode = .pen
                    }
                    toolButton(
                        title: "Eraser",
                        icon: "eraser.fill",
                        active: store.toolMode == .eraser
                    ) {
                        store.toolMode = .eraser
                    }
                }
                .padding(4)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

                iconActionButton(icon: "arrow.uturn.backward", label: "Undo", disabled: !store.canUndo) {
                    store.undo()
                }
                iconActionButton(icon: "arrow.uturn.forward", label: "Redo", disabled: !store.canRedo) {
                    store.redo()
                }
                iconActionButton(icon: "trash", label: "Clear", disabled: store.drawing.strokes.isEmpty) {
                    store.clearCanvas()
                }

                Spacer()

                // Primary Evaluate Ink CTA
                Button {
                    isExprFocused = false
                    Task { await store.evaluateInk() }
                } label: {
                    HStack(spacing: 10) {
                        if store.isOcrRunning {
                            ProgressView()
                                .tint(.white)
                                .scaleEffect(1.0)
                        } else {
                            Image(systemName: "sparkles")
                                .font(.system(size: 20, weight: .semibold))
                        }
                        Text(store.isOcrRunning ? "Reading Ink…" : "Evaluate Ink")
                            .font(.system(size: 20, weight: .bold, design: .rounded))
                    }
                    .foregroundStyle(.white)
                    .padding(.horizontal, 22)
                    .frame(height: 52)
                    .background(theme.accentCobalt, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                    .shadow(color: theme.accentCobalt.opacity(0.24), radius: 8, y: 3)
                }
                .buttonStyle(.plain)
                .disabled(store.isOcrRunning)
            }

            // PencilKit Canvas Card
            ZStack {
                RoundedRectangle(cornerRadius: 20, style: .continuous)
                    .fill(theme.elevatedCard)
                    .overlay(
                        RoundedRectangle(cornerRadius: 20, style: .continuous)
                            .stroke(theme.borderSubtle, lineWidth: 1.5)
                    )

                PaperDotGrid(dotColor: theme.canvasDotColor)
                    .clipShape(RoundedRectangle(cornerRadius: 20, style: .continuous))

                if store.drawing.strokes.isEmpty {
                    VStack(spacing: 10) {
                        Image(systemName: "pencil.and.scribble")
                            .font(.system(size: 40, weight: .light))
                            .foregroundStyle(theme.secondaryInk.opacity(0.45))
                        Text("Write an infinitesimal expression with Apple Pencil or finger")
                            .font(.system(size: 20, weight: .medium, design: .rounded))
                            .foregroundStyle(theme.secondaryInk.opacity(0.65))
                            .multilineTextAlignment(.center)
                        Text("Examples: 1/(1+exp(-Hx)) · dstep(x) · (1 + ε)³ · diff(x⁴, x, 2)")
                            .font(.system(size: 18, design: .monospaced))
                            .foregroundStyle(theme.secondaryInk.opacity(0.55))
                    }
                    .padding(24)
                    .allowsHitTesting(false)
                }

                PencilCanvasView(
                    drawing: $store.drawing,
                    toolMode: store.toolMode,
                    inkColor: theme.canvasInkUIColor,
                    controller: store.canvasController,
                    onDrawingChanged: { store.syncUndoState() }
                )
                .clipShape(RoundedRectangle(cornerRadius: 20, style: .continuous))
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)

            // 1-Tap Starter Chips Row (with Apple Pencil / pointer hover explanation + (?) finger legend)
            VStack(alignment: .leading, spacing: 6) {
                HStack(spacing: 8) {
                    Text("1-TAP STARTERS")
                        .font(.system(size: 14, weight: .bold, design: .rounded))
                        .tracking(1.0)
                        .foregroundStyle(theme.secondaryInk)

                    if let activeHint = (hoveredChip ?? InfPadPresets.starterChips.first(where: { $0.expr == store.expressionText }))?.hint {
                        Text("·  \(activeHint)")
                            .font(.system(size: 14, weight: .medium, design: .rounded))
                            .foregroundStyle(hoveredChip != nil ? theme.accentCobalt : theme.secondaryInk)
                            .lineLimit(1)
                            .truncationMode(.tail)
                    }

                    Spacer(minLength: 4)

                    Button {
                        showStarterLegend.toggle()
                    } label: {
                        Image(systemName: "questionmark.circle")
                            .font(.system(size: 18, weight: .semibold))
                            .foregroundStyle(theme.accentCobalt)
                    }
                    .buttonStyle(.plain)
                    .accessibilityLabel("Starter expression explanations")
                    .popover(isPresented: $showStarterLegend, arrowEdge: .bottom) {
                        starterLegendPopover
                    }
                }

                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 10) {
                        ForEach(InfPadPresets.starterChips) { chip in
                            let isSelected = store.expressionText == chip.expr
                            let isHovered = hoveredChip?.id == chip.id
                            Button {
                                isExprFocused = false
                                Task { await store.selectStarterChip(chip) }
                            } label: {
                                Text(chip.label)
                                    .font(.system(size: 19, weight: .semibold, design: .monospaced))
                                    .foregroundStyle(theme.primaryInk)
                                    .padding(.horizontal, 16)
                                    .padding(.vertical, 11)
                                    .background(
                                        isHovered ? theme.accentCobalt.opacity(0.10) : theme.surfaceCard,
                                        in: RoundedRectangle(cornerRadius: 12, style: .continuous)
                                    )
                                    .overlay(
                                        RoundedRectangle(cornerRadius: 12, style: .continuous)
                                            .stroke(
                                                (isSelected || isHovered) ? theme.accentCobalt : theme.borderSubtle,
                                                lineWidth: (isSelected || isHovered) ? 2 : 1
                                            )
                                    )
                            }
                            .buttonStyle(.plain)
                            .help(chip.hint)
                            .onHover { inside in
                                if inside {
                                    hoveredChip = chip
                                } else if hoveredChip?.id == chip.id {
                                    hoveredChip = nil
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private var starterLegendPopover: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Starter Expressions")
                .font(.system(size: 20, weight: .bold, design: .rounded))
                .foregroundStyle(theme.primaryInk)

            ForEach(InfPadPresets.starterChips) { chip in
                Button {
                    showStarterLegend = false
                    isExprFocused = false
                    Task { await store.selectStarterChip(chip) }
                } label: {
                    VStack(alignment: .leading, spacing: 3) {
                        Text(chip.label)
                            .font(.system(size: 17, weight: .bold, design: .monospaced))
                            .foregroundStyle(theme.accentCobalt)
                        Text(chip.hint)
                            .font(.system(size: 15, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                            .fixedSize(horizontal: false, vertical: true)
                    }
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(10)
                    .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                }
                .buttonStyle(.plain)
            }
        }
        .padding(18)
        .frame(width: 480)
        .background(theme.paperBackground)
    }

    // MARK: - Right Pane: Recognized Expr + Lean 4 FastLC Result + H ↦ N Slider + History

    private var rightInspectorPane: some View {
        ScrollView(.vertical, showsIndicators: true) {
            VStack(spacing: 14) {
                expressionEditorCard

                if let err = store.errorMessage {
                    errorBanner(err)
                }

                if let ev = store.evalResult, ev.ok, let plot = ev.plot, ev.isFunction {
                    FunctionPlotCard(
                        eval: ev,
                        plot: plot,
                        theme: theme,
                        currentN: Int(store.sliderN.rounded()),
                        latencyText: (store.ocrMs != nil || store.leanMs != nil) ? latencyBadgeText : nil
                    )

                    finiteSliderCard
                } else {
                    resultCard

                    finiteSliderCard
                }

                historyStripCard
            }
            .padding(.bottom, 12)
        }
    }

    private var expressionEditorCard: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Text("EXPRESSION")
                    .font(.system(size: 15, weight: .bold, design: .rounded))
                    .tracking(1.0)
                    .foregroundStyle(theme.secondaryInk)

                Spacer()

                if let rec = store.recognizedExpr, !rec.isEmpty {
                    Text("OCR: \(rec)")
                        .font(.system(size: 15, weight: .medium, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                        .lineLimit(1)
                }
            }

            HStack(spacing: 10) {
                TextField("e.g. dstep(0) or (1 + eps)^(-1)", text: $store.expressionText)
                    .font(.system(size: 24, weight: .semibold, design: .monospaced))
                    .foregroundStyle(theme.primaryInk)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled()
                    .focused($isExprFocused)
                    .submitLabel(.go)
                    .onSubmit {
                        Task { await store.evaluateExpression() }
                    }
                    .padding(.horizontal, 14)
                    .frame(height: 54)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                    .overlay(
                        RoundedRectangle(cornerRadius: 12, style: .continuous)
                            .stroke(isExprFocused ? theme.accentCobalt : theme.borderSubtle, lineWidth: isExprFocused ? 2 : 1)
                    )

                Button {
                    isExprFocused = false
                    Task { await store.evaluateExpression() }
                } label: {
                    HStack(spacing: 6) {
                        if store.isEvaluating {
                            ProgressView().tint(.white)
                        } else {
                            Image(systemName: "play.fill")
                                .font(.system(size: 17, weight: .bold))
                        }
                        Text("Re-Eval")
                            .font(.system(size: 19, weight: .bold, design: .rounded))
                    }
                    .foregroundStyle(.white)
                    .padding(.horizontal, 18)
                    .frame(height: 54)
                    .background(theme.accentCobalt, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                }
                .buttonStyle(.plain)
                .disabled(store.isEvaluating)
            }

            // Quick math symbol rail for rapid expression tweaking
            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    ForEach(InfPadPresets.quickSymbols, id: \.self) { sym in
                        Button {
                            store.insertSymbol(sym)
                        } label: {
                            Text(sym)
                                .font(.system(size: 18, weight: .medium, design: .monospaced))
                                .foregroundStyle(theme.primaryInk)
                                .padding(.horizontal, 12)
                                .padding(.vertical, 7)
                                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 9, style: .continuous))
                                .overlay(RoundedRectangle(cornerRadius: 9, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                        }
                        .buttonStyle(.plain)
                    }
                }
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    private func errorBanner(_ message: String) -> some View {
        HStack(alignment: .top, spacing: 10) {
            Image(systemName: "exclamationmark.triangle.fill")
                .font(.system(size: 20))
                .foregroundStyle(theme.errorRed)
            Text(message)
                .font(.system(size: 18, weight: .medium, design: .rounded))
                .foregroundStyle(theme.errorRed)
                .fixedSize(horizontal: false, vertical: true)
            Spacer()
        }
        .padding(14)
        .background(theme.errorRed.opacity(0.10), in: RoundedRectangle(cornerRadius: 14, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.errorRed.opacity(0.3), lineWidth: 1))
    }

    private var resultCard: some View {
        VStack(alignment: .leading, spacing: 14) {
            HStack(spacing: 10) {
                Text("EXACT LEAN 4 FastLC")
                    .font(.system(size: 15, weight: .bold, design: .rounded))
                    .tracking(1.0)
                    .foregroundStyle(theme.secondaryInk)

                if let ev = store.evalResult, ev.ok {
                    let style = theme.regimeStyle(ev.regime)
                    Text(style.label)
                        .font(.system(size: 15, weight: .bold, design: .rounded))
                        .foregroundStyle(style.fg)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 4)
                        .background(style.bg, in: Capsule())
                }

                Spacer()

                // Latency badge
                if store.ocrMs != nil || store.leanMs != nil {
                    Text(latencyBadgeText)
                        .font(.system(size: 16, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.secondaryInk)
                        .padding(.horizontal, 10)
                        .padding(.vertical, 4)
                        .background(theme.elevatedCard, in: Capsule())
                        .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                }
            }

            if let ev = store.evalResult, ev.ok {
                let rawDisplay = store.showApprox ? (ev.approx ?? ev.exact ?? "") : (ev.exact ?? "")
                let preview = store.showApprox ? (head: rawDisplay, tailCount: 0) : ev.splitExactPreview(maxVisibleTerms: 3)
                let shownText = (store.expandExactTail || preview.tailCount == 0) ? rawDisplay : "\(preview.head) …"

                Text(shownText)
                    .font(.system(size: 30, weight: .semibold, design: .monospaced))
                    .foregroundStyle(theme.primaryInk)
                    .lineSpacing(6)
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(16)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

                // Expand/collapse long rational tail + Exact/Approx + Copy controls
                HStack(spacing: 10) {
                    if preview.tailCount > 0 && !store.showApprox {
                        Button {
                            withAnimation(.easeInOut(duration: 0.18)) {
                                store.expandExactTail.toggle()
                            }
                        } label: {
                            HStack(spacing: 6) {
                                Image(systemName: store.expandExactTail ? "chevron.up" : "chevron.down")
                                Text(store.expandExactTail ? "Hide rational tail" : "Show +\(preview.tailCount) exact terms")
                            }
                            .font(.system(size: 17, weight: .semibold, design: .rounded))
                            .foregroundStyle(theme.accentCobalt)
                            .padding(.horizontal, 14)
                            .padding(.vertical, 8)
                            .background(theme.accentCobalt.opacity(0.12), in: Capsule())
                        }
                        .buttonStyle(.plain)
                    }

                    Spacer()

                    Button {
                        store.showApprox.toggle()
                    } label: {
                        Text(store.showApprox ? "Show Exact Q" : "Decimal")
                            .font(.system(size: 17, weight: .semibold, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                            .padding(.horizontal, 14)
                            .padding(.vertical, 8)
                            .background(theme.elevatedCard, in: Capsule())
                            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                    }
                    .buttonStyle(.plain)

                    Button {
                        UIPasteboard.general.string = rawDisplay
                        copiedFeedback = true
                        DispatchQueue.main.asyncAfter(deadline: .now() + 1.4) {
                            copiedFeedback = false
                        }
                    } label: {
                        Label(copiedFeedback ? "Copied" : "Copy", systemImage: copiedFeedback ? "checkmark" : "doc.on.doc")
                            .font(.system(size: 17, weight: .semibold, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                            .padding(.horizontal, 14)
                            .padding(.vertical, 8)
                            .background(theme.elevatedCard, in: Capsule())
                            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                    }
                    .buttonStyle(.plain)
                }

                // Compact metadata row
                if ev.kind == "num" {
                    HStack(spacing: 12) {
                        metaPill(label: "Dominant", value: ev.dominant ?? "0")
                        metaPill(label: "Std Part", value: ev.std_part ?? "∞ (none)")
                        metaPill(label: "Terms", value: "\(ev.term_count ?? ev.terms?.count ?? 0)")
                    }
                }
            } else {
                Text("Write an expression on the left or tap a starter chip to evaluate in Lean 4.")
                    .font(.system(size: 20, weight: .medium, design: .rounded))
                    .foregroundStyle(theme.secondaryInk)
                    .padding(16)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    private var latencyBadgeText: String {
        let leanStr = store.leanMs.map { String(format: "%.2f ms", $0) } ?? "—"
        if let ocr = store.ocrMs {
            let ocrStr = ocr >= 1000 ? String(format: "%.2fs", ocr / 1000.0) : String(format: "%.0f ms", ocr)
            return "OCR \(ocrStr) · Lean \(leanStr)"
        }
        return "Lean \(leanStr)"
    }

    private func metaPill(label: String, value: String) -> some View {
        VStack(alignment: .leading, spacing: 3) {
            Text(label.uppercased())
                .font(.system(size: 13, weight: .bold, design: .rounded))
                .foregroundStyle(theme.secondaryInk)
            Text(value)
                .font(.system(size: 18, weight: .semibold, design: .monospaced))
                .foregroundStyle(theme.primaryInk)
                .lineLimit(1)
                .minimumScaleFactor(0.75)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .padding(.horizontal, 12)
        .padding(.vertical, 9)
        .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    // MARK: - Interactive H ↦ N Slider Card

    private var finiteSliderCard: some View {
        let isFn = store.evalResult?.isFunction == true
        return VStack(alignment: .leading, spacing: 12) {
            HStack(alignment: .firstTextBaseline) {
                Text(isFn ? "LIVE SCALE  H ↦ N  (TIGHTENS STEP)" : "FINITE PROJECTION  H ↦ N")
                    .font(.system(size: 15, weight: .bold, design: .rounded))
                    .tracking(1.0)
                    .foregroundStyle(theme.secondaryInk)

                Spacer()

                Text("N = \(Int(store.sliderN.rounded()))")
                    .font(.system(size: 20, weight: .bold, design: .monospaced))
                    .monospacedDigit()
                    .foregroundStyle(theme.accentCobalt)
            }

            HStack(alignment: .firstTextBaseline, spacing: 12) {
                if isFn {
                    Text(store.evalResult?.exact ?? "f(x) at H ↦ \(Int(store.sliderN.rounded()))")
                        .font(.system(size: 18, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.primaryInk)
                        .lineLimit(1)
                        .minimumScaleFactor(0.75)
                } else {
                    Text(formattedFiniteReadout)
                        .font(.system(size: 28, weight: .bold, design: .monospaced))
                        .monospacedDigit()
                        .foregroundStyle(theme.primaryInk)
                        .lineLimit(1)
                        .minimumScaleFactor(0.7)
                }

                Spacer()

                HStack(spacing: 6) {
                    ForEach([10, 100, 500, 1000], id: \.self) { snap in
                        Button {
                            store.sliderN = Double(snap)
                            Task { await store.commitSliderN() }
                        } label: {
                            Text("\(snap)")
                                .font(.system(size: 16, weight: .semibold, design: .monospaced))
                                .foregroundStyle(Int(store.sliderN.rounded()) == snap ? .white : theme.primaryInk)
                                .padding(.horizontal, 11)
                                .padding(.vertical, 7)
                                .background(
                                    Int(store.sliderN.rounded()) == snap ? theme.accentCobalt : theme.elevatedCard,
                                    in: RoundedRectangle(cornerRadius: 9, style: .continuous)
                                )
                                .overlay(
                                    RoundedRectangle(cornerRadius: 9, style: .continuous)
                                        .stroke(theme.borderSubtle, lineWidth: 1)
                                )
                        }
                        .buttonStyle(.plain)
                    }
                }
            }

            Slider(
                value: $store.sliderN,
                in: 10...1000,
                step: 1,
                onEditingChanged: { editing in
                    store.isScrubbingN = editing
                    if !editing {
                        Task { await store.commitSliderN() }
                    }
                }
            )
            .tint(theme.accentCobalt)
            .onChange(of: store.sliderN) { _, _ in
                if store.isScrubbingN {
                    store.scheduleDebouncedPlotUpdate()
                }
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    private var formattedFiniteReadout: String {
        guard let ev = store.evalResult, ev.ok else { return "—" }
        if ev.kind == "bool" { return ev.exact ?? "—" }
        guard let val = store.displayedFiniteValue() else { return "overflow" }
        if abs(val) >= 1e7 || (val != 0 && abs(val) < 1e-4) {
            return String(format: "%.6e", val)
        }
        return String(format: "%.6f", val)
    }

    // MARK: - History Strip Card

    private var historyStripCard: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Text("HISTORY")
                    .font(.system(size: 15, weight: .bold, design: .rounded))
                    .tracking(1.0)
                    .foregroundStyle(theme.secondaryInk)
                Spacer()
                Text("\(store.history.count) saved")
                    .font(.system(size: 15, weight: .medium, design: .rounded))
                    .foregroundStyle(theme.secondaryInk)
            }

            if store.history.isEmpty {
                Text("Evaluated expressions and ink drawings will appear here for 1-tap reload.")
                    .font(.system(size: 17, design: .rounded))
                    .foregroundStyle(theme.secondaryInk)
                    .padding(.vertical, 6)
            } else {
                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 12) {
                        ForEach(store.history) { entry in
                            Button {
                                Task { await store.loadHistoryEntry(entry) }
                            } label: {
                                HStack(spacing: 10) {
                                    if let img = store.thumbnailImage(for: entry) {
                                        Image(uiImage: img)
                                            .resizable()
                                            .scaledToFit()
                                            .frame(width: 68, height: 48)
                                            .background(Color.white, in: RoundedRectangle(cornerRadius: 8))
                                            .overlay(RoundedRectangle(cornerRadius: 8).stroke(theme.borderSubtle, lineWidth: 1))
                                    }
                                    VStack(alignment: .leading, spacing: 4) {
                                        Text(entry.expression)
                                            .font(.system(size: 17, weight: .bold, design: .monospaced))
                                            .foregroundStyle(theme.primaryInk)
                                            .lineLimit(1)
                                        Text(entry.exactSummary)
                                            .font(.system(size: 15, design: .monospaced))
                                            .foregroundStyle(theme.secondaryInk)
                                            .lineLimit(1)
                                    }
                                }
                                .frame(minWidth: 170, maxWidth: 260, alignment: .leading)
                                .padding(.horizontal, 12)
                                .padding(.vertical, 10)
                                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                                .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                            }
                            .buttonStyle(.plain)
                        }
                    }
                }
            }
        }
        .padding(16)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    // MARK: - Toolbar Helper Buttons

    private func toolButton(title: String, icon: String, active: Bool, action: @escaping () -> Void) -> some View {
        Button(action: action) {
            HStack(spacing: 6) {
                Image(systemName: icon)
                    .font(.system(size: 18, weight: .semibold))
                Text(title)
                    .font(.system(size: 18, weight: .semibold, design: .rounded))
            }
            .foregroundStyle(active ? .white : theme.primaryInk)
            .padding(.horizontal, 14)
            .frame(height: 44)
            .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
        }
        .buttonStyle(.plain)
    }

    private func iconActionButton(icon: String, label: String, disabled: Bool, action: @escaping () -> Void) -> some View {
        Button(action: action) {
            Image(systemName: icon)
                .font(.system(size: 20, weight: .semibold))
                .foregroundStyle(disabled ? theme.secondaryInk.opacity(0.35) : theme.primaryInk)
                .frame(width: 48, height: 50)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
        }
        .buttonStyle(.plain)
        .disabled(disabled)
        .accessibilityLabel(label)
    }
}
