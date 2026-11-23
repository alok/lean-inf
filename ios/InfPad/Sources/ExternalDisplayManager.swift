import AVKit
import SwiftUI
import UIKit

/// Native iOS AirPlay route picker button (`AVRoutePickerView`) for the presentation toolbar.
struct AirPlayRoutePickerButton: UIViewRepresentable {
    var tintColor: UIColor
    var activeTintColor: UIColor

    func makeUIView(context: Context) -> AVRoutePickerView {
        let picker = AVRoutePickerView()
        picker.tintColor = tintColor
        picker.activeTintColor = activeTintColor
        picker.prioritizesVideoDevices = true
        return picker
    }

    func updateUIView(_ uiView: AVRoutePickerView, context: Context) {
        uiView.tintColor = tintColor
        uiView.activeTintColor = activeTintColor
    }
}

/// Manages BOTH non-mirrored AirPlay displays AND wired USB-C -> HDMI external displays.
/// When an external display is connected, renders ONLY the clean Audience View (Slide OR live Calculator output),
/// hiding all speaker notes, timers, and the iPad's private Split workspace.
@MainActor
final class ExternalDisplayManager: ObservableObject {
    static let shared = ExternalDisplayManager()

    @Published private(set) var isExternalDisplayConnected: Bool = false

    private var externalWindow: UIWindow?
    private weak var store: InfPadStore?
    private var observersInstalled = false

    private init() {}

    func attach(store: InfPadStore) {
        self.store = store
        if !observersInstalled {
            observersInstalled = true
            let nc = NotificationCenter.default
            nc.addObserver(self, selector: #selector(displayEnvironmentChanged), name: UIScene.willConnectNotification, object: nil)
            nc.addObserver(self, selector: #selector(displayEnvironmentChanged), name: UIScene.didDisconnectNotification, object: nil)
            nc.addObserver(self, selector: #selector(displayEnvironmentChanged), name: UIScreen.didConnectNotification, object: nil)
            nc.addObserver(self, selector: #selector(displayEnvironmentChanged), name: UIScreen.didDisconnectNotification, object: nil)
        }
        refreshExternalScenes()
    }

    @objc private func displayEnvironmentChanged(_ notification: Notification) {
        refreshExternalScenes()
    }

    private func refreshExternalScenes() {
        guard let store else { return }

        // Detect external AirPlay or wired USB-C -> HDMI window scene
        let windowScenes = UIApplication.shared.connectedScenes.compactMap { $0 as? UIWindowScene }
        let mainScreen = windowScenes
            .first(where: { $0.session.role == .windowApplication })?.screen
        let externalScene = windowScenes.first { scene in
            if scene.session.role == .windowExternalDisplayNonInteractive {
                return true
            }
            if let mainScreen, scene.screen !== mainScreen {
                return true
            }
            return false
        }

        guard let scene = externalScene else {
            externalWindow?.isHidden = true
            externalWindow = nil
            isExternalDisplayConnected = false
            return
        }

        if externalWindow?.windowScene === scene {
            isExternalDisplayConnected = true
            return
        }

        let win = UIWindow(windowScene: scene)
        let audienceRoot = ExternalAudienceStageRoot(store: store)
        let host = UIHostingController(rootView: audienceRoot)
        host.view.backgroundColor = .clear
        win.rootViewController = host
        win.isHidden = false
        externalWindow = win
        isExternalDisplayConnected = true
    }
}

/// Clean audience-only root view rendered on an external AirPlay or wired USB-C -> HDMI TV/projector.
private struct ExternalAudienceStageRoot: View {
    @Bindable var store: InfPadStore

    var body: some View {
        ZStack {
            store.theme.paperBackground.ignoresSafeArea()
            if store.externalOutputMode == .slide {
                SlideAudienceView(
                    store: store,
                    slide: SlideDeck.slides[store.currentSlideIndex],
                    interactiveDemoButtons: false,
                    allowAnnotationInput: false
                )
                .aspectRatio(16.0 / 9.0, contentMode: .fit)
                .padding(24)
            } else {
                // Clean audience Calculator view: expression + Lean 4 exact result / plot / heatmap (zero chrome!)
                VStack(spacing: 18) {
                    HStack {
                        Text(store.expressionText.isEmpty ? "InfPad · Lean 4 FastLC" : store.expressionText)
                            .font(.system(size: 36, weight: .bold, design: .monospaced))
                            .foregroundStyle(store.theme.primaryInk)
                            .lineLimit(1)
                            .minimumScaleFactor(0.6)
                        Spacer()
                        Text("Lean 4.36.0")
                            .font(.system(size: 20, weight: .bold, design: .monospaced))
                            .foregroundStyle(store.theme.accentCobalt)
                            .padding(.horizontal, 14)
                            .padding(.vertical, 6)
                            .background(store.theme.surfaceCard, in: Capsule())
                    }

                    if let ev = store.evalResult, ev.ok {
                        if ev.isFunction, let plot = ev.plot {
                            FunctionPlotCard(
                                eval: ev,
                                plot: plot,
                                theme: store.theme,
                                currentN: Int(store.sliderN.rounded()),
                                latencyText: store.leanMs.map { String(format: "Lean %.2f ms", $0) }
                            )
                        } else if ev.isHeatmap {
                            HeatmapPlotCard(
                                eval: ev,
                                theme: store.theme,
                                currentN: Int(store.sliderN.rounded()),
                                latencyText: store.leanMs.map { String(format: "Lean %.2f ms", $0) }
                            )
                        } else {
                            VStack(spacing: 16) {
                                Text(ev.exact ?? ev.approx ?? "")
                                    .font(.system(size: 40, weight: .semibold, design: .monospaced))
                                    .foregroundStyle(store.theme.primaryInk)
                                    .multilineTextAlignment(.leading)
                                    .frame(maxWidth: .infinity, alignment: .leading)
                                    .padding(24)
                                    .background(store.theme.elevatedCard, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
                                if ev.isFiniteProjectionPlot, let plot = ev.plot {
                                    ConstantScalePlotCard(
                                        eval: ev,
                                        plot: plot,
                                        theme: store.theme,
                                        currentN: Int(store.sliderN.rounded())
                                    )
                                }
                            }
                        }
                    } else {
                        Spacer()
                        Text("Ready for live Lean 4 FastLC evaluation")
                            .font(.system(size: 30, weight: .medium, design: .rounded))
                            .foregroundStyle(store.theme.secondaryInk)
                        Spacer()
                    }
                    Spacer(minLength: 0)
                }
                .padding(32)
            }
        }
        .preferredColorScheme(store.isDark ? .dark : .light)
    }
}
