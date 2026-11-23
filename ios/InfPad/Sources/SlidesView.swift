import PencilKit
import SwiftUI
import UIKit

enum SlideInkTool: String, CaseIterable, Identifiable {
    case pen
    case highlighter
    case eraser

    var id: String { rawValue }
}

// MARK: - Transparent Apple Pencil Annotation Overlay for Slides

struct SlideAnnotationCanvas: UIViewRepresentable {
    @Binding var drawing: PKDrawing
    var tool: SlideInkTool
    var pencilOnly: Bool
    var isDark: Bool
    var allowsInput: Bool

    func makeCoordinator() -> Coordinator { Coordinator(parent: self) }

    func makeUIView(context: Context) -> PKCanvasView {
        let canvas = PKCanvasView()
        canvas.backgroundColor = .clear
        canvas.isOpaque = false
        canvas.isScrollEnabled = false
        canvas.drawingPolicy = pencilOnly ? .pencilOnly : .anyInput
        canvas.isUserInteractionEnabled = allowsInput
        canvas.delegate = context.coordinator
        canvas.drawing = drawing
        canvas.tool = currentTool()
        return canvas
    }

    func updateUIView(_ canvas: PKCanvasView, context: Context) {
        context.coordinator.parent = self
        canvas.drawingPolicy = pencilOnly ? .pencilOnly : .anyInput
        canvas.isUserInteractionEnabled = allowsInput
        canvas.tool = currentTool()

        if !context.coordinator.isInternalUpdate && canvas.drawing.dataRepresentation() != drawing.dataRepresentation() {
            context.coordinator.isInternalUpdate = true
            canvas.drawing = drawing
            context.coordinator.isInternalUpdate = false
        }
    }

    private func currentTool() -> PKTool {
        switch tool {
        case .pen:
            let col = isDark
                ? UIColor(red: 0.99, green: 0.55, blue: 0.35, alpha: 1.0)
                : UIColor(red: 0.86, green: 0.15, blue: 0.15, alpha: 0.95)
            return PKInkingTool(.pen, color: col, width: 5.0)
        case .highlighter:
            let col = UIColor(red: 0.98, green: 0.80, blue: 0.08, alpha: 0.45)
            return PKInkingTool(.marker, color: col, width: 22.0)
        case .eraser:
            return PKEraserTool(.vector)
        }
    }

    final class Coordinator: NSObject, PKCanvasViewDelegate {
        var parent: SlideAnnotationCanvas
        var isInternalUpdate = false

        init(parent: SlideAnnotationCanvas) { self.parent = parent }

        func canvasViewDrawingDidChange(_ canvasView: PKCanvasView) {
            guard !isInternalUpdate else { return }
            isInternalUpdate = true
            parent.drawing = canvasView.drawing
            isInternalUpdate = false
        }
    }
}

// MARK: - Compact Side-by-Side Split Slide Pane (Left 46% in `Split` Mode)

struct SplitSlidePane: View {
    @Bindable var store: InfPadStore
    @State private var showNotes = true

    private var theme: InfTheme { store.theme }
    private var currentSlide: InfSlide { SlideDeck.slides[store.currentSlideIndex] }

    var body: some View {
        VStack(spacing: 10) {
            // Compact nav + ink + Stage Clean bar
            HStack(spacing: 6) {
                Button { store.prevSlide() } label: {
                    Image(systemName: "chevron.left")
                        .font(.system(size: 16, weight: .bold))
                        .frame(width: 36, height: 36)
                }
                .disabled(store.currentSlideIndex == 0)

                Text("\(store.currentSlideIndex + 1)/\(SlideDeck.slides.count)")
                    .font(.system(size: 16, weight: .bold, design: .monospaced))
                    .monospacedDigit()

                Button { store.nextSlide() } label: {
                    Image(systemName: "chevron.right")
                        .font(.system(size: 16, weight: .bold))
                        .frame(width: 36, height: 36)
                }
                .disabled(store.currentSlideIndex >= SlideDeck.slides.count - 1)

                Divider().frame(height: 18)

                Button { store.slideAnnotationTool = .pen } label: {
                    Image(systemName: "pencil.tip")
                        .font(.system(size: 15, weight: .semibold))
                        .foregroundStyle(store.slideAnnotationTool == .pen ? .white : theme.primaryInk)
                        .frame(width: 34, height: 34)
                        .background(store.slideAnnotationTool == .pen ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 8))
                }
                .buttonStyle(.plain)

                Button { store.clearSlideDrawing(index: store.currentSlideIndex) } label: {
                    Image(systemName: "trash")
                        .font(.system(size: 15, weight: .semibold))
                        .frame(width: 34, height: 34)
                }
                .buttonStyle(.plain)

                Spacer()

                Button {
                    withAnimation(.easeInOut(duration: 0.15)) { showNotes.toggle() }
                } label: {
                    Text(showNotes ? "Hide Notes" : "Notes")
                        .font(.system(size: 14, weight: .semibold, design: .rounded))
                        .padding(.horizontal, 10)
                        .padding(.vertical, 6)
                        .background(theme.elevatedCard, in: Capsule())
                        .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
                }
                .buttonStyle(.plain)

                Button {
                    store.activeTab = .slides
                    store.isAirPlayClean = true
                } label: {
                    Image(systemName: "tv")
                        .font(.system(size: 15, weight: .bold))
                        .foregroundStyle(.white)
                        .frame(width: 36, height: 34)
                        .background(theme.accentCobalt, in: RoundedRectangle(cornerRadius: 8))
                }
                .buttonStyle(.plain)
                .accessibilityLabel("Stage Clean Fullscreen")
            }
            .foregroundStyle(theme.primaryInk)
            .padding(.horizontal, 10)
            .padding(.vertical, 6)
            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            // 16:9 Live Slide Stage with Pencil overlay
            SlideAudienceView(
                store: store,
                slide: currentSlide,
                interactiveDemoButtons: true,
                allowAnnotationInput: true
            )
            .aspectRatio(16.0 / 9.0, contentMode: .fit)
            .gesture(
                DragGesture(minimumDistance: 45)
                    .onEnded { val in
                        if val.translation.width < -45 { store.nextSlide() }
                        else if val.translation.width > 45 { store.prevSlide() }
                    }
            )

            // Compact Speaker Notes & Pace Anchor beneath the slide
            if showNotes {
                ScrollView(.vertical, showsIndicators: true) {
                    VStack(alignment: .leading, spacing: 8) {
                        HStack {
                            Text("SPEAKER CUES  ·  \(currentSlide.startTime) -> \(currentSlide.gateTime)")
                                .font(.system(size: 13, weight: .bold, design: .monospaced))
                                .foregroundStyle(theme.accentCobalt)
                            Spacer()
                            Text(currentSlide.notes.paceAnchor)
                                .font(.system(size: 13, weight: .semibold, design: .rounded))
                                .foregroundStyle(theme.secondaryInk)
                        }
                        Text(currentSlide.notes.broadStroke)
                            .font(.system(size: 16, weight: .medium, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                        ForEach(currentSlide.notes.microdetails, id: \.self) { line in
                            HStack(alignment: .top, spacing: 6) {
                                Text("•").foregroundStyle(theme.accentCobalt)
                                Text(line)
                                    .font(.system(size: 14.5, design: .rounded))
                                    .foregroundStyle(theme.secondaryInk)
                            }
                        }
                    }
                    .padding(12)
                    .frame(maxWidth: .infinity, alignment: .leading)
                }
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
            } else {
                Spacer(minLength: 0)
            }
        }
    }
}

// MARK: - Main AirPlay Slides View (Presenter Split + 1-Tap Stage Clean)

struct SlidesView: View {
    @Bindable var store: InfPadStore
    @ObservedObject private var externalDisplay = ExternalDisplayManager.shared

    @State private var elapsedSeconds: Int = 0
    @State private var timerRunning: Bool = false
    @State private var showQASheet: Bool = false

    private let ticker = Timer.publish(every: 1, on: .main, in: .common).autoconnect()
    private var theme: InfTheme { store.theme }
    private var currentSlide: InfSlide { SlideDeck.slides[store.currentSlideIndex] }

    var body: some View {
        ZStack {
            theme.paperBackground.ignoresSafeArea()

            if store.isAirPlayClean {
                airPlayCleanStageView
            } else {
                presenterSplitView
            }
        }
        .onReceive(ticker) { _ in
            if timerRunning {
                elapsedSeconds += 1
            }
        }
    }

    // MARK: - 1-Tap Stage Clean Fullscreen View (for Screen Mirroring)

    private var airPlayCleanStageView: some View {
        ZStack(alignment: .bottomTrailing) {
            VStack {
                Spacer(minLength: 4)
                SlideAudienceView(
                    store: store,
                    slide: currentSlide,
                    interactiveDemoButtons: true,
                    allowAnnotationInput: true
                )
                .aspectRatio(16.0 / 9.0, contentMode: .fit)
                .padding(.horizontal, 18)
                Spacer(minLength: 4)
            }
            .gesture(
                DragGesture(minimumDistance: 50)
                    .onEnded { val in
                        if val.translation.width < -50 { store.nextSlide() }
                        else if val.translation.width > 50 { store.prevSlide() }
                    }
            )

            // Minimal unobtrusive bottom-right floating stage pill
            HStack(spacing: 8) {
                Button { store.prevSlide() } label: {
                    Image(systemName: "chevron.left")
                        .font(.system(size: 16, weight: .bold))
                        .frame(width: 34, height: 34)
                }
                .disabled(store.currentSlideIndex == 0)

                Text("\(store.currentSlideIndex + 1)/\(SlideDeck.slides.count)")
                    .font(.system(size: 15, weight: .bold, design: .monospaced))
                    .monospacedDigit()

                Button { store.nextSlide() } label: {
                    Image(systemName: "chevron.right")
                        .font(.system(size: 16, weight: .bold))
                        .frame(width: 34, height: 34)
                }
                .disabled(store.currentSlideIndex >= SlideDeck.slides.count - 1)

                Divider().frame(height: 18)

                Button { store.clearSlideDrawing(index: store.currentSlideIndex) } label: {
                    Image(systemName: "eraser")
                        .font(.system(size: 15, weight: .semibold))
                        .frame(width: 32, height: 32)
                }

                Button { store.jumpToCalculator() } label: {
                    Text("Calc")
                        .font(.system(size: 15, weight: .bold, design: .rounded))
                        .padding(.horizontal, 10)
                        .padding(.vertical, 6)
                        .background(theme.accentCobalt, in: Capsule())
                        .foregroundStyle(.white)
                }

                Button { store.isAirPlayClean = false } label: {
                    Image(systemName: "arrow.down.right.and.arrow.up.left")
                        .font(.system(size: 15, weight: .bold))
                        .frame(width: 34, height: 34)
                }
                .accessibilityLabel("Exit Stage Clean")
            }
            .foregroundStyle(theme.primaryInk)
            .padding(.horizontal, 12)
            .padding(.vertical, 7)
            .background(theme.surfaceCard.opacity(0.92), in: Capsule())
            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))
            .shadow(color: Color.black.opacity(0.10), radius: 8, y: 2)
            .padding(18)
        }
    }

    // MARK: - Presenter Split View (Slide + Live Timer + Structured Speaker Notes)

    private var presenterSplitView: some View {
        VStack(spacing: 0) {
            slidesToolbar

            GeometryReader { geo in
                let isLandscape = geo.size.width >= geo.size.height
                if isLandscape {
                    HStack(spacing: 16) {
                        presenterSlideColumn
                            .frame(width: geo.size.width * 0.62)
                        presenterNotesColumn
                            .frame(maxWidth: .infinity)
                    }
                    .padding(.horizontal, 16)
                    .padding(.vertical, 12)
                } else {
                    VStack(spacing: 14) {
                        presenterSlideColumn
                            .frame(height: geo.size.height * 0.46)
                        presenterNotesColumn
                            .frame(maxHeight: .infinity)
                    }
                    .padding(.horizontal, 16)
                    .padding(.vertical, 12)
                }
            }
        }
    }

    private var slidesToolbar: some View {
        HStack(spacing: 10) {
            HStack(spacing: 4) {
                Button { store.prevSlide() } label: {
                    Image(systemName: "chevron.left")
                        .font(.system(size: 18, weight: .bold))
                        .frame(width: 40, height: 40)
                }
                .disabled(store.currentSlideIndex == 0)

                Text("\(store.currentSlideIndex + 1) / \(SlideDeck.slides.count)")
                    .font(.system(size: 18, weight: .bold, design: .monospaced))
                    .monospacedDigit()
                    .frame(minWidth: 64)

                Button { store.nextSlide() } label: {
                    Image(systemName: "chevron.right")
                        .font(.system(size: 18, weight: .bold))
                        .frame(width: 40, height: 40)
                }
                .disabled(store.currentSlideIndex >= SlideDeck.slides.count - 1)
            }
            .foregroundStyle(theme.primaryInk)
            .padding(.horizontal, 6)
            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            HStack(spacing: 4) {
                inkToolPill(.pen, icon: "pencil.tip", label: "Pen")
                inkToolPill(.highlighter, icon: "highlighter", label: "Hi")
                inkToolPill(.eraser, icon: "eraser.fill", label: "Erase")
            }
            .padding(3)
            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            Button {
                store.clearSlideDrawing(index: store.currentSlideIndex)
            } label: {
                Image(systemName: "trash")
                    .font(.system(size: 17, weight: .semibold))
                    .foregroundStyle(theme.primaryInk)
                    .frame(width: 42, height: 42)
                    .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
            }
            .buttonStyle(.plain)

            Button {
                store.slidePencilOnly.toggle()
            } label: {
                HStack(spacing: 5) {
                    Image(systemName: store.slidePencilOnly ? "applepencil.tip" : "hand.draw")
                    Text(store.slidePencilOnly ? "Pencil" : "Touch")
                }
                .font(.system(size: 15, weight: .semibold, design: .rounded))
                .foregroundStyle(theme.primaryInk)
                .padding(.horizontal, 11)
                .frame(height: 42)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
            }
            .buttonStyle(.plain)

            Spacer()

            // Subtle display mode indicator (Extended TV vs Mirrored)
            HStack(spacing: 6) {
                Circle()
                    .fill(externalDisplay.isExternalDisplayConnected ? theme.successGreen : theme.secondaryInk.opacity(0.5))
                    .frame(width: 8, height: 8)
                Text(externalDisplay.isExternalDisplayConnected ? "Extended TV" : "Mirrored")
                    .font(.system(size: 14, weight: .semibold, design: .rounded))
                    .foregroundStyle(externalDisplay.isExternalDisplayConnected ? theme.successGreen : theme.secondaryInk)
            }
            .padding(.horizontal, 10)
            .padding(.vertical, 6)
            .background(theme.surfaceCard, in: Capsule())
            .overlay(Capsule().stroke(theme.borderSubtle, lineWidth: 1))

            // Native AVKit AirPlay Route Picker
            AirPlayRoutePickerButton(
                tintColor: theme.canvasInkUIColor,
                activeTintColor: UIColor(red: 0.114, green: 0.306, blue: 0.847, alpha: 1.0)
            )
            .frame(width: 42, height: 42)
            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))

            Button {
                store.isAirPlayClean = true
            } label: {
                HStack(spacing: 7) {
                    Image(systemName: "tv")
                        .font(.system(size: 17, weight: .bold))
                    Text("Stage Clean")
                        .font(.system(size: 17, weight: .bold, design: .rounded))
                }
                .foregroundStyle(.white)
                .padding(.horizontal, 16)
                .frame(height: 42)
                .background(theme.accentCobalt, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
            }
            .buttonStyle(.plain)
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 10)
        .overlay(alignment: .bottom) {
            Rectangle().fill(theme.borderSubtle).frame(height: 1)
        }
    }

    private func inkToolPill(_ tool: SlideInkTool, icon: String, label: String) -> some View {
        let active = store.slideAnnotationTool == tool
        return Button {
            store.slideAnnotationTool = tool
        } label: {
            HStack(spacing: 4) {
                Image(systemName: icon).font(.system(size: 15, weight: .semibold))
                Text(label).font(.system(size: 15, weight: .semibold, design: .rounded))
            }
            .foregroundStyle(active ? .white : theme.primaryInk)
            .padding(.horizontal, 10)
            .frame(height: 36)
            .background(active ? theme.accentCobalt : Color.clear, in: RoundedRectangle(cornerRadius: 9, style: .continuous))
        }
        .buttonStyle(.plain)
    }

    private var presenterSlideColumn: some View {
        VStack(spacing: 12) {
            SlideAudienceView(
                store: store,
                slide: currentSlide,
                interactiveDemoButtons: true,
                allowAnnotationInput: true
            )
            .aspectRatio(16.0 / 9.0, contentMode: .fit)
            .frame(maxWidth: .infinity, maxHeight: .infinity)
            .gesture(
                DragGesture(minimumDistance: 50)
                    .onEnded { val in
                        if val.translation.width < -50 { store.nextSlide() }
                        else if val.translation.width > 50 { store.prevSlide() }
                    }
            )

            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    ForEach(SlideDeck.slides) { s in
                        let isCur = s.id == store.currentSlideIndex
                        Button {
                            store.currentSlideIndex = s.id
                        } label: {
                            HStack(spacing: 6) {
                                Text("\(s.id + 1)")
                                    .font(.system(size: 14, weight: .bold, design: .monospaced))
                                    .foregroundStyle(isCur ? .white : theme.accentCobalt)
                                    .frame(width: 24, height: 24)
                                    .background(isCur ? theme.accentCobalt : theme.accentCobalt.opacity(0.12), in: Circle())
                                Text(s.title)
                                    .font(.system(size: 14, weight: isCur ? .bold : .medium, design: .rounded))
                                    .foregroundStyle(theme.primaryInk)
                                    .lineLimit(1)
                            }
                            .padding(.horizontal, 10)
                            .padding(.vertical, 7)
                            .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                            .overlay(
                                RoundedRectangle(cornerRadius: 10, style: .continuous)
                                    .stroke(isCur ? theme.accentCobalt : theme.borderSubtle, lineWidth: isCur ? 2 : 1)
                            )
                        }
                        .buttonStyle(.plain)
                    }
                }
            }
        }
    }

    private var presenterNotesColumn: some View {
        ScrollView(.vertical, showsIndicators: true) {
            VStack(alignment: .leading, spacing: 12) {
                timerCard

                noteBlock(title: "BROAD STROKE", accent: theme.accentCobalt) {
                    Text(currentSlide.notes.broadStroke)
                        .font(.system(size: 18, weight: .medium, design: .rounded))
                        .foregroundStyle(theme.primaryInk)
                }

                noteBlock(title: "MICRODETAILS", accent: theme.primaryInk) {
                    VStack(alignment: .leading, spacing: 7) {
                        ForEach(currentSlide.notes.microdetails, id: \.self) { line in
                            HStack(alignment: .top, spacing: 8) {
                                Text("•").foregroundStyle(theme.accentCobalt)
                                Text(line)
                                    .font(.system(size: 16, design: .rounded))
                                    .foregroundStyle(theme.primaryInk)
                            }
                        }
                    }
                }

                HStack(alignment: .top, spacing: 10) {
                    noteBlock(title: "CUT IF BEHIND", accent: theme.errorRed) {
                        Text(currentSlide.notes.cutIfBehind)
                            .font(.system(size: 15, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                    }
                    noteBlock(title: "EXPAND IF AHEAD", accent: theme.successGreen) {
                        Text(currentSlide.notes.expandIfAhead)
                            .font(.system(size: 15, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                    }
                }

                noteBlock(title: "PACE ANCHOR", accent: theme.secondaryInk) {
                    HStack {
                        Text(currentSlide.notes.paceAnchor)
                            .font(.system(size: 16, weight: .semibold, design: .monospaced))
                            .foregroundStyle(theme.primaryInk)
                        Spacer()
                        if store.currentSlideIndex + 1 < SlideDeck.slides.count {
                            let next = SlideDeck.slides[store.currentSlideIndex + 1]
                            Text("Next: \(next.title)")
                                .font(.system(size: 15, weight: .medium, design: .rounded))
                                .foregroundStyle(theme.secondaryInk)
                                .lineLimit(1)
                        }
                    }
                }

                if !currentSlide.qaItems.isEmpty {
                    VStack(alignment: .leading, spacing: 10) {
                        Button {
                            withAnimation(.easeInOut(duration: 0.16)) { showQASheet.toggle() }
                        } label: {
                            HStack {
                                Text("Q&A CHEAT SHEET (PRESENTER ONLY)")
                                    .font(.system(size: 14, weight: .bold, design: .rounded))
                                    .tracking(0.8)
                                    .foregroundStyle(theme.accentCobalt)
                                Spacer()
                                Image(systemName: showQASheet ? "chevron.up" : "chevron.down")
                                    .foregroundStyle(theme.accentCobalt)
                            }
                        }
                        .buttonStyle(.plain)

                        if showQASheet {
                            ForEach(currentSlide.qaItems) { item in
                                VStack(alignment: .leading, spacing: 4) {
                                    Text(item.question)
                                        .font(.system(size: 16, weight: .bold, design: .rounded))
                                        .foregroundStyle(theme.primaryInk)
                                    Text(item.answer)
                                        .font(.system(size: 15, design: .rounded))
                                        .foregroundStyle(theme.secondaryInk)
                                }
                                .padding(10)
                                .frame(maxWidth: .infinity, alignment: .leading)
                                .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                            }
                        }
                    }
                    .padding(14)
                    .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }
            }
            .padding(.bottom, 12)
        }
    }

    private var timerCard: some View {
        let pace = paceStatus()
        return VStack(alignment: .leading, spacing: 10) {
            HStack(alignment: .firstTextBaseline) {
                Text("\(formatMMSS(elapsedSeconds)) / 13:00")
                    .font(.system(size: 28, weight: .bold, design: .monospaced))
                    .monospacedDigit()
                    .foregroundStyle(timerColor())

                Spacer()

                Text(pace.label)
                    .font(.system(size: 14, weight: .bold, design: .rounded))
                    .foregroundStyle(pace.fg)
                    .padding(.horizontal, 10)
                    .padding(.vertical, 5)
                    .background(pace.bg, in: Capsule())
            }

            HStack(spacing: 10) {
                Button {
                    timerRunning.toggle()
                } label: {
                    Label(timerRunning ? "Pause" : "Start", systemImage: timerRunning ? "pause.fill" : "play.fill")
                        .font(.system(size: 16, weight: .bold, design: .rounded))
                        .foregroundStyle(.white)
                        .padding(.horizontal, 14)
                        .padding(.vertical, 8)
                        .background(theme.accentCobalt, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                }
                .buttonStyle(.plain)

                Button {
                    timerRunning = false
                    elapsedSeconds = 0
                } label: {
                    Text("Reset")
                        .font(.system(size: 16, weight: .semibold, design: .rounded))
                        .foregroundStyle(theme.primaryInk)
                        .padding(.horizontal, 12)
                        .padding(.vertical, 8)
                        .background(theme.elevatedCard, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                        .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }
                .buttonStyle(.plain)

                Spacer()

                Text("Gate \(currentSlide.startTime) -> \(currentSlide.gateTime)")
                    .font(.system(size: 15, weight: .semibold, design: .monospaced))
                    .foregroundStyle(theme.secondaryInk)
            }
        }
        .padding(14)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    private func timerColor() -> Color {
        if elapsedSeconds >= 13 * 60 { return theme.errorRed }
        if elapsedSeconds >= 11 * 60 { return Color.orange }
        return theme.primaryInk
    }

    private func paceStatus() -> (label: String, fg: Color, bg: Color) {
        let delta = elapsedSeconds - currentSlide.gateSeconds
        if elapsedSeconds == 0 {
            return ("READY", theme.accentCobalt, theme.accentCobalt.opacity(0.14))
        }
        if delta > 20 {
            return ("BEHIND +\(delta)s", theme.errorRed, theme.errorRed.opacity(0.14))
        }
        if delta < -45 {
            return ("AHEAD \(-delta)s", theme.successGreen, theme.successGreen.opacity(0.14))
        }
        return ("ON PACE", theme.successGreen, theme.successGreen.opacity(0.14))
    }

    private func formatMMSS(_ s: Int) -> String {
        String(format: "%02d:%02d", s / 60, s % 60)
    }

    private func noteBlock<Content: View>(title: String, accent: Color, @ViewBuilder content: () -> Content) -> some View {
        VStack(alignment: .leading, spacing: 6) {
            Text(title)
                .font(.system(size: 13, weight: .bold, design: .rounded))
                .tracking(0.8)
                .foregroundStyle(accent)
            content()
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .padding(13)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 14, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }
}

// MARK: - Monospaced Source Code Card for Slides 4, 5, 6

private struct SlideCodeCard: View {
    let badge: String
    let code: String
    let accent: Color
    let theme: InfTheme
    let compact: Bool

    var body: some View {
        VStack(alignment: .leading, spacing: compact ? 4 : 6) {
            Text(badge)
                .font(.system(size: compact ? 10.5 : 13, weight: .bold, design: .monospaced))
                .foregroundStyle(accent)
                .padding(.horizontal, 8)
                .padding(.vertical, 2)
                .background(accent.opacity(0.13), in: Capsule())

            Text(code)
                .font(.system(size: compact ? 10.5 : 13.5, weight: .medium, design: .monospaced))
                .foregroundStyle(theme.primaryInk)
                .lineSpacing(2)
                .fixedSize(horizontal: false, vertical: true)
                .minimumScaleFactor(0.75)
        }
        .padding(compact ? 8 : 11)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(theme.paperBackground, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(accent.opacity(0.28), lineWidth: 1))
    }
}

// MARK: - Clean 16:9 Audience Slide Face + Bespoke SwiftUI Visuals + Pencil Overlay

struct SlideAudienceView: View {
    @Bindable var store: InfPadStore
    let slide: InfSlide
    let interactiveDemoButtons: Bool
    let allowAnnotationInput: Bool

    private var theme: InfTheme { store.theme }

    private var drawingBinding: Binding<PKDrawing> {
        Binding(
            get: { store.slideDrawings[slide.id] ?? PKDrawing() },
            set: { store.slideDrawings[slide.id] = $0 }
        )
    }

    var body: some View {
        GeometryReader { geo in
            let compact = geo.size.width < 760
            let titleSize: CGFloat = compact ? 22 : 34
            let thesisSize: CGFloat = compact ? 14 : 19.5
            let detailSize: CGFloat = compact ? 12 : 16

            ZStack {
                RoundedRectangle(cornerRadius: 22, style: .continuous)
                    .fill(theme.elevatedCard)
                    .overlay(
                        RoundedRectangle(cornerRadius: 22, style: .continuous)
                            .stroke(theme.borderSubtle, lineWidth: 1.5)
                    )
                    .shadow(color: Color.black.opacity(0.06), radius: 14, y: 4)

                PaperDotGrid(dotColor: theme.canvasDotColor.opacity(0.55))
                    .clipShape(RoundedRectangle(cornerRadius: 22, style: .continuous))

                VStack(alignment: .leading, spacing: compact ? 8 : 14) {
                    HStack(alignment: .center) {
                        Text(slide.title)
                            .font(.system(size: titleSize, weight: .bold, design: .rounded))
                            .foregroundStyle(theme.primaryInk)
                            .lineLimit(2)
                            .minimumScaleFactor(0.72)

                        Spacer(minLength: 10)

                        Text("\(slide.id + 1) / \(SlideDeck.slides.count)")
                            .font(.system(size: compact ? 12.5 : 16, weight: .bold, design: .monospaced))
                            .foregroundStyle(theme.secondaryInk)
                            .padding(.horizontal, 10)
                            .padding(.vertical, 4)
                            .background(theme.surfaceCard, in: Capsule())
                    }

                    Text(slide.thesis)
                        .font(.system(size: thesisSize, weight: .medium, design: .rounded))
                        .foregroundStyle(theme.secondaryInk)
                        .lineSpacing(2)
                        .fixedSize(horizontal: false, vertical: true)

                    slideVisual(compact: compact)
                        .frame(maxWidth: .infinity, maxHeight: .infinity)

                    if slide.visual != .liveDemoLauncher {
                        VStack(alignment: .leading, spacing: compact ? 4 : 7) {
                            ForEach(slide.microdetails, id: \.self) { detail in
                                HStack(alignment: .top, spacing: 8) {
                                    Circle()
                                        .fill(theme.accentCobalt)
                                        .frame(width: compact ? 5 : 7, height: compact ? 5 : 7)
                                        .padding(.top, compact ? 5 : 7)
                                    Text(detail)
                                        .font(.system(size: detailSize, weight: .medium, design: .rounded))
                                        .foregroundStyle(theme.primaryInk)
                                        .lineLimit(2)
                                        .minimumScaleFactor(0.78)
                                }
                            }
                        }
                        .padding(compact ? 8 : 12)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .background(theme.surfaceCard.opacity(0.85), in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                    }
                }
                .padding(compact ? 14 : 26)

                SlideAnnotationCanvas(
                    drawing: drawingBinding,
                    tool: store.slideAnnotationTool,
                    pencilOnly: store.slidePencilOnly,
                    isDark: store.isDark,
                    allowsInput: allowAnnotationInput
                )
                .clipShape(RoundedRectangle(cornerRadius: 22, style: .continuous))
                .allowsHitTesting(allowAnnotationInput && (slide.demoActions.isEmpty || store.slidePencilOnly))
            }
        }
    }

    // MARK: - Bespoke Slide Visual Diagrams (with Real Repo Code Cards on Slides 4, 5, 6)

    @ViewBuilder
    private func slideVisual(compact: Bool) -> some View {
        switch slide.visual {
        case .titleHero:
            titleHeroVisual(compact: compact)
        case .continuumCut:
            continuumCutVisual(compact: compact)
        case .stepToDirac:
            stepToDiracVisual(compact: compact)
        case .firstTriesTimeline:
            firstTriesVisual(compact: compact)
        case .speedupBars:
            speedupBarsVisual(compact: compact)
        case .grindAndFloatLib:
            grindAndFloatLibVisual(compact: compact)
        case .verificationPillars:
            verificationPillarsVisual(compact: compact)
        case .liveDemoLauncher:
            liveDemoLauncherVisual(compact: compact)
        }
    }

    private func titleHeroVisual(compact: Bool) -> some View {
        VStack(spacing: compact ? 12 : 20) {
            Text("H · ε = 1")
                .font(.system(size: compact ? 42 : 70, weight: .bold, design: .monospaced))
                .foregroundStyle(theme.accentCobalt)
                .padding(.horizontal, 28)
                .padding(.vertical, compact ? 12 : 20)
                .background(theme.accentCobalt.opacity(0.09), in: RoundedRectangle(cornerRadius: 18, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 18, style: .continuous).stroke(theme.accentCobalt.opacity(0.28), lineWidth: 1.5))

            HStack(spacing: compact ? 8 : 16) {
                heroPill(value: "112.6 ms -> 0.38 ms", label: "Dense 512×512 mul (296×)", compact: compact)
                heroPill(value: "187 / 187", label: "7-engine diff parity", compact: compact)
                heroPill(value: "0 sorry", label: "Core + 24 FloatLib thms", compact: compact)
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private func heroPill(value: String, label: String, compact: Bool) -> some View {
        VStack(spacing: 4) {
            Text(value)
                .font(.system(size: compact ? 14 : 22, weight: .bold, design: .monospaced))
                .foregroundStyle(theme.primaryInk)
                .minimumScaleFactor(0.72)
                .lineLimit(1)
            Text(label)
                .font(.system(size: compact ? 11 : 14, weight: .medium, design: .rounded))
                .foregroundStyle(theme.secondaryInk)
                .lineLimit(1)
        }
        .frame(maxWidth: .infinity)
        .padding(.vertical, compact ? 8 : 14)
        .padding(.horizontal, 8)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
    }

    private func continuumCutVisual(compact: Bool) -> some View {
        VStack(spacing: compact ? 6 : 12) {
            Canvas { ctx, size in
                let padX: CGFloat = 32
                let midY = size.height * 0.56
                let w = max(60, size.width - padX * 2)

                var axis = Path()
                axis.move(to: CGPoint(x: padX, y: midY))
                axis.addLine(to: CGPoint(x: padX + w, y: midY))
                ctx.stroke(axis, with: .color(theme.primaryInk), lineWidth: 3)

                let ticks = 28
                for i in 0...ticks {
                    let x = padX + CGFloat(i) / CGFloat(ticks) * w
                    let isEnd = (i == 0 || i == ticks)
                    let h: CGFloat = isEnd ? 20 : 10
                    var t = Path()
                    t.move(to: CGPoint(x: x, y: midY - h))
                    t.addLine(to: CGPoint(x: x, y: midY + h))
                    ctx.stroke(t, with: .color(isEnd ? theme.primaryInk : theme.accentCobalt.opacity(0.65)), lineWidth: isEnd ? 3 : 1.8)
                }

                let cellX0 = padX + 10.0 / CGFloat(ticks) * w
                let cellX1 = padX + 11.0 / CGFloat(ticks) * w
                let rect = CGRect(x: cellX0, y: midY - 24, width: max(8, cellX1 - cellX0), height: 24)
                ctx.fill(Path(rect), with: .color(theme.accentCobalt.opacity(0.28)))
                ctx.stroke(Path(rect), with: .color(theme.accentCobalt), lineWidth: 2)

                ctx.draw(Text("a").font(.system(size: compact ? 14 : 18, weight: .bold, design: .monospaced)).foregroundColor(theme.primaryInk), at: CGPoint(x: padX, y: midY + 30))
                ctx.draw(Text("b").font(.system(size: compact ? 14 : 18, weight: .bold, design: .monospaced)).foregroundColor(theme.primaryInk), at: CGPoint(x: padX + w, y: midY + 30))
                ctx.draw(Text("width ε = 1/H").font(.system(size: compact ? 13 : 17, weight: .bold, design: .monospaced)).foregroundColor(theme.accentCobalt), at: CGPoint(x: (cellX0 + cellX1) / 2, y: midY - 36))
                ctx.draw(Text("H hyperfinite pieces").font(.system(size: compact ? 13 : 17, weight: .semibold, design: .rounded)).foregroundColor(theme.secondaryInk), at: CGPoint(x: padX + w * 0.72, y: midY - 34))
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)

            HStack(spacing: 12) {
                Label("Integrals -> hyperfinite sums", systemImage: "sum")
                Spacer()
                Label("ODEs -> H-step loops", systemImage: "arrow.triangle.2.circlepath")
                Spacer()
                Label("Ordered subring ℚ[H^ℚ]", systemImage: "function")
            }
            .font(.system(size: compact ? 11.5 : 16, weight: .semibold, design: .monospaced))
            .foregroundStyle(theme.accentCobalt)
            .padding(.horizontal, 12)
            .padding(.vertical, 7)
            .background(theme.accentCobalt.opacity(0.08), in: RoundedRectangle(cornerRadius: 10, style: .continuous))
        }
    }

    private func stepToDiracVisual(compact: Bool) -> some View {
        VStack(spacing: compact ? 6 : 10) {
            HStack(spacing: compact ? 10 : 18) {
                VStack(alignment: .leading, spacing: 5) {
                    Text("Lₕ(x) = 1 / (1 + exp(-H·x))")
                        .font(.system(size: compact ? 12 : 16, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                    Canvas { ctx, sz in
                        let pad: CGFloat = 16
                        let rect = CGRect(x: pad, y: pad, width: sz.width - pad * 2, height: sz.height - pad * 2)
                        var guide = Path()
                        guide.move(to: CGPoint(x: rect.midX, y: rect.minY))
                        guide.addLine(to: CGPoint(x: rect.midX, y: rect.maxY))
                        ctx.stroke(guide, with: .color(theme.secondaryInk.opacity(0.35)), style: StrokeStyle(lineWidth: 1.2, dash: [4, 4]))

                        var curve = Path()
                        for i in 0...100 {
                            let u = -1.0 + 2.0 * Double(i) / 100.0
                            let y = 1.0 / (1.0 + exp(-28.0 * u))
                            let px = rect.minX + CGFloat((u + 1.0) / 2.0) * rect.width
                            let py = rect.maxY - CGFloat(y) * rect.height
                            if i == 0 { curve.move(to: CGPoint(x: px, y: py)) }
                            else { curve.addLine(to: CGPoint(x: px, y: py)) }
                        }
                        ctx.stroke(curve, with: .color(theme.accentCobalt), style: StrokeStyle(lineWidth: 3.0, lineCap: .round))
                        let dot = CGRect(x: rect.midX - 5, y: rect.midY - 5, width: 10, height: 10)
                        ctx.fill(Path(ellipseIn: dot), with: .color(theme.accentCobalt))
                    }
                    .background(theme.paperBackground, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }

                VStack(alignment: .leading, spacing: 5) {
                    Text("Lₕ'(0) = H/4   (width ε, area 1)")
                        .font(.system(size: compact ? 12 : 16, weight: .bold, design: .monospaced))
                        .foregroundStyle(Color(red: 0.604, green: 0.204, blue: 0.071))
                    Canvas { ctx, sz in
                        let pad: CGFloat = 16
                        let rect = CGRect(x: pad, y: pad, width: sz.width - pad * 2, height: sz.height - pad * 2)
                        var guide = Path()
                        guide.move(to: CGPoint(x: rect.midX, y: rect.minY))
                        guide.addLine(to: CGPoint(x: rect.midX, y: rect.maxY))
                        ctx.stroke(guide, with: .color(theme.secondaryInk.opacity(0.35)), style: StrokeStyle(lineWidth: 1.2, dash: [4, 4]))

                        var curve = Path()
                        for i in 0...120 {
                            let u = -1.0 + 2.0 * Double(i) / 120.0
                            let s = 1.0 / (1.0 + exp(-28.0 * u))
                            let y = 4.0 * s * (1.0 - s)
                            let px = rect.minX + CGFloat((u + 1.0) / 2.0) * rect.width
                            let py = rect.maxY - CGFloat(y) * rect.height
                            if i == 0 { curve.move(to: CGPoint(x: px, y: py)) }
                            else { curve.addLine(to: CGPoint(x: px, y: py)) }
                        }
                        var fill = curve
                        fill.addLine(to: CGPoint(x: rect.maxX, y: rect.maxY))
                        fill.addLine(to: CGPoint(x: rect.minX, y: rect.maxY))
                        fill.closeSubpath()
                        let spikeColor = Color(red: 0.76, green: 0.25, blue: 0.05)
                        ctx.fill(fill, with: .color(spikeColor.opacity(0.14)))
                        ctx.stroke(curve, with: .color(spikeColor), style: StrokeStyle(lineWidth: 3.0, lineCap: .round))
                    }
                    .background(theme.paperBackground, in: RoundedRectangle(cornerRadius: 10, style: .continuous))
                    .overlay(RoundedRectangle(cornerRadius: 10, style: .continuous).stroke(theme.borderSubtle, lineWidth: 1))
                }
            }

            if interactiveDemoButtons, let action = slide.demoActions.first {
                HStack {
                    Spacer()
                    Button {
                        store.jumpToCalculator(expr: action.expr)
                    } label: {
                        HStack(spacing: 7) {
                            Image(systemName: "bolt.fill")
                            Text(action.title)
                        }
                        .font(.system(size: compact ? 14 : 17, weight: .bold, design: .rounded))
                        .foregroundStyle(.white)
                        .padding(.horizontal, 16)
                        .padding(.vertical, 8)
                        .background(theme.accentCobalt, in: Capsule())
                    }
                    .buttonStyle(.plain)
                }
            }
        }
    }

    // Slide 4: Real 2024 vs 2026 Lean Source Code Cards
    private func firstTriesVisual(compact: Bool) -> some View {
        VStack(spacing: compact ? 8 : 12) {
            SlideCodeCard(
                badge: "Jul 2024 · 0088b08 · Lean 4.10 + Mathlib",
                code: """
                import Mathlib
                abbrev CoeffMap := Lean.HashMap Exponent Coeff  -- TODO use RbMap instead bc sorted?
                syntax "#[" term " | " compClause,* "]" : term  -- custom macro_rules DSL
                """,
                accent: Color(red: 0.604, green: 0.204, blue: 0.071),
                theme: theme,
                compact: compact
            )

            SlideCodeCard(
                badge: "Nov 2026 · VerifiedRefactor.lean · Lean 4.36, 0 Mathlib",
                code: """
                structure FastLC where
                  terms : TermList          -- strictly descending, nonzero
                  wf : TermList.WF terms    -- Prop: erased at runtime
                @[csimp] theorem coeff_eq_coeffWF : @FastLC.coeff = @FastLC.coeffWF
                """,
                accent: theme.accentCobalt,
                theme: theme,
                compact: compact
            )
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    // Slide 5: Concrete Speedup Bars + Real Equivalence Proof Code Card
    private func speedupBarsVisual(compact: Bool) -> some View {
        let rows: [(name: String, before: String, after: String, speedup: String, afterFrac: CGFloat)] = [
            ("mul_dense 512", "112.6 ms", "0.38 ms", "296× (324× iso)", 0.025),
            ("inv 40", "2.79 ms", "6.6 µs", "425× (361× iso)", 0.020),
            ("mul_sparse 64", "2.48 ms", "178 µs", "13.9×", 0.072),
            ("signum 128", "35.1 µs", "0.06 µs", "636×", 0.015),
        ]

        return VStack(spacing: compact ? 6 : 9) {
            ForEach(rows, id: \.name) { row in
                HStack(spacing: 10) {
                    Text(row.name)
                        .font(.system(size: compact ? 11.5 : 15, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.primaryInk)
                        .frame(width: compact ? 102 : 145, alignment: .leading)

                    GeometryReader { g in
                        VStack(alignment: .leading, spacing: 3) {
                            RoundedRectangle(cornerRadius: 4, style: .continuous)
                                .fill(theme.secondaryInk.opacity(0.28))
                                .frame(width: g.size.width * 0.92, height: compact ? 7 : 10)
                            RoundedRectangle(cornerRadius: 4, style: .continuous)
                                .fill(theme.accentCobalt)
                                .frame(width: max(10, g.size.width * 0.92 * row.afterFrac), height: compact ? 7 : 10)
                        }
                        .frame(maxHeight: .infinity, alignment: .center)
                    }

                    Text("\(row.before) -> \(row.after)  \(row.speedup)")
                        .font(.system(size: compact ? 10.5 : 14, weight: .semibold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                        .frame(width: compact ? 170 : 255, alignment: .trailing)
                        .lineLimit(1)
                }
                .padding(.horizontal, 10)
                .padding(.vertical, compact ? 4 : 6)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 9, style: .continuous))
            }

            SlideCodeCard(
                badge: "VerifiedRefactor.lean + Kronecker.lean · Closed-Loop Oracle",
                code: """
                theorem mul_eq_mulNaive (x y : FastLC) : x * y = mulNaive x y
                theorem powFast_eq_powNaive (x : FastLC) (n : Nat) : powFast x n = powNaive x n
                theorem newton_order_doubles ...  -- quadratic convergence of invNewton
                """,
                accent: theme.accentCobalt,
                theme: theme,
                compact: compact
            )
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    // Slide 6: Architecture Split + Real grind / FloatLib Code Card
    private func grindAndFloatLibVisual(compact: Bool) -> some View {
        VStack(spacing: compact ? 8 : 11) {
            HStack(spacing: compact ? 10 : 16) {
                VStack(alignment: .leading, spacing: compact ? 4 : 7) {
                    Text("ZERO-MATHLIB CORE")
                        .font(.system(size: compact ? 11.5 : 14, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.accentCobalt)
                    Text("Lean 4.36 CommRing & OrderedRing")
                        .font(.system(size: compact ? 14 : 19, weight: .bold, design: .rounded))
                        .foregroundStyle(theme.primaryInk)
                    Text("23 GrindShowcase thms / 32 by grind · 54/54 jobs, 0 warnings")
                        .font(.system(size: compact ? 11.5 : 14.5, design: .rounded))
                        .foregroundStyle(theme.secondaryInk)
                }
                .padding(compact ? 9 : 13)
                .frame(maxWidth: .infinity, alignment: .topLeading)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.accentCobalt.opacity(0.32), lineWidth: 1.2))

                VStack(alignment: .leading, spacing: compact ? 4 : 7) {
                    Text("NESTED float-proofs/ (FloatLib)")
                        .font(.system(size: compact ? 11.5 : 14, weight: .bold, design: .monospaced))
                        .foregroundStyle(theme.successGreen)
                    Text("24 Zero-Sorry IEEE-754 Theorems")
                        .font(.system(size: compact ? 14 : 19, weight: .bold, design: .rounded))
                        .foregroundStyle(theme.primaryInk)
                    Text("Binary64 Sum2, < 4 u64 sigmoidB64, N = 2⁶⁰ cancellation")
                        .font(.system(size: compact ? 11.5 : 14.5, design: .rounded))
                        .foregroundStyle(theme.secondaryInk)
                }
                .padding(compact ? 9 : 13)
                .frame(maxWidth: .infinity, alignment: .topLeading)
                .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
                .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(theme.successGreen.opacity(0.32), lineWidth: 1.2))
            }

            SlideCodeCard(
                badge: "Grind.lean + float-proofs/DiracBridge.lean",
                code: """
                instance : Lean.Grind.OrderedRing FastLC  -- 0 Mathlib
                theorem grind_H_mul_eps_add_one : infH * infEps + 1 = 2 := by grind
                theorem diracCenter_at_100_certified :
                  24.99979 < (evalFiniteSum2 diracCenterLC b100).toReal ∧ ...
                """,
                accent: theme.successGreen,
                theme: theme,
                compact: compact
            )
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private func verificationPillarsVisual(compact: Bool) -> some View {
        HStack(spacing: compact ? 8 : 14) {
            pillarCard(
                badge: "KERNEL",
                headline: "167+ tests",
                body: "0 sorry, 0 @[extern], 0 native_decide.\nStandard 3 axioms only.\nTCB outside kernel: compiler, GMP, parser, Float.",
                color: theme.accentCobalt,
                compact: compact
            )
            pillarCard(
                badge: "7-ENGINE DIFF",
                headline: "187 / 187",
                body: "FastLC 187/187, Web JS 187/187, HashMap 158/158 (0 bugs).\nCrowell JS: 24 bugs despite 29/29 Test.js.\n2024 Lean: 25, Python: 31.",
                color: theme.successGreen,
                compact: compact
            )
            pillarCard(
                badge: "58-CASE 8-AXIS",
                headline: "17.57×",
                body: "1,508.5 -> 85.8 µs geomean, 0 regressions, Peak RSS 45 MB.\nCaught Axis-3 den != 1 (1,249 -> 106 µs) + GMP 2³¹-1 cliff.",
                color: Color(red: 0.604, green: 0.204, blue: 0.071),
                compact: compact
            )
        }
    }

    private func pillarCard(badge: String, headline: String, body: String, color: Color, compact: Bool) -> some View {
        VStack(alignment: .leading, spacing: compact ? 5 : 9) {
            Text(badge)
                .font(.system(size: compact ? 11 : 13, weight: .bold, design: .monospaced))
                .foregroundStyle(color)
                .padding(.horizontal, 8)
                .padding(.vertical, 3)
                .background(color.opacity(0.14), in: Capsule())
            Text(headline)
                .font(.system(size: compact ? 20 : 32, weight: .bold, design: .monospaced))
                .foregroundStyle(theme.primaryInk)
            Text(body)
                .font(.system(size: compact ? 11.5 : 15, design: .rounded))
                .foregroundStyle(theme.secondaryInk)
                .lineSpacing(2)
            Spacer(minLength: 0)
        }
        .padding(compact ? 9 : 13)
        .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
        .background(theme.surfaceCard, in: RoundedRectangle(cornerRadius: 12, style: .continuous))
        .overlay(RoundedRectangle(cornerRadius: 12, style: .continuous).stroke(color.opacity(0.32), lineWidth: 1.4))
    }

    private func liveDemoLauncherVisual(compact: Bool) -> some View {
        let cols = [
            GridItem(.flexible(), spacing: compact ? 8 : 14),
            GridItem(.flexible(), spacing: compact ? 8 : 14),
            GridItem(.flexible(), spacing: compact ? 8 : 14),
        ]
        return LazyVGrid(columns: cols, spacing: compact ? 8 : 14) {
            ForEach(slide.demoActions) { action in
                Button {
                    guard interactiveDemoButtons else { return }
                    store.jumpToCalculator(expr: action.expr, clearCanvasForDrawing: action.clearForPencil)
                } label: {
                    VStack(alignment: .leading, spacing: compact ? 4 : 7) {
                        HStack {
                            Image(systemName: action.clearForPencil ? "pencil.and.scribble" : "bolt.fill")
                                .font(.system(size: compact ? 14 : 20, weight: .bold))
                                .foregroundStyle(action.clearForPencil ? .white : theme.accentCobalt)
                            Spacer()
                            Image(systemName: "arrow.up.right")
                                .font(.system(size: 13, weight: .bold))
                                .foregroundStyle(action.clearForPencil ? .white.opacity(0.85) : theme.secondaryInk)
                        }
                        Text(action.title)
                            .font(.system(size: compact ? 13.5 : 19, weight: .bold, design: .monospaced))
                            .foregroundStyle(action.clearForPencil ? .white : theme.primaryInk)
                            .lineLimit(1)
                            .minimumScaleFactor(0.72)
                        Text(action.subtitle)
                            .font(.system(size: compact ? 11 : 14, design: .rounded))
                            .foregroundStyle(action.clearForPencil ? .white.opacity(0.9) : theme.secondaryInk)
                            .lineLimit(2)
                    }
                    .frame(maxWidth: .infinity, minHeight: compact ? 74 : 110, alignment: .topLeading)
                    .padding(compact ? 10 : 14)
                    .background(
                        action.clearForPencil ? theme.accentCobalt : theme.surfaceCard,
                        in: RoundedRectangle(cornerRadius: 14, style: .continuous)
                    )
                    .overlay(
                        RoundedRectangle(cornerRadius: 14, style: .continuous)
                            .stroke(action.clearForPencil ? theme.accentCobalt : theme.borderSubtle, lineWidth: 1.4)
                    )
                }
                .buttonStyle(.plain)
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }
}
