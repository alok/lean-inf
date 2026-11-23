import AVKit
import SwiftUI
import UIKit

/// Native iOS AirPlay route picker button (`AVRoutePickerView`) for the Slides toolbar.
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

/// Manages an external non-mirrored AirPlay / HDMI display when connected,
/// rendering ONLY the clean 16:9 `SlideAudienceView` (slide + live Pencil ink, zero speaker notes/timer)
/// while iPad remains in full Presenter Console mode.
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
            NotificationCenter.default.addObserver(
                self,
                selector: #selector(sceneDidConnect(_:)),
                name: UIScene.willConnectNotification,
                object: nil
            )
            NotificationCenter.default.addObserver(
                self,
                selector: #selector(sceneDidDisconnect(_:)),
                name: UIScene.didDisconnectNotification,
                object: nil
            )
        }
        refreshExternalScenes()
    }

    @objc private func sceneDidConnect(_ notification: Notification) {
        refreshExternalScenes()
    }

    @objc private func sceneDidDisconnect(_ notification: Notification) {
        if let scene = notification.object as? UIWindowScene, externalWindow?.windowScene === scene {
            externalWindow?.isHidden = true
            externalWindow = nil
            isExternalDisplayConnected = false
        }
        refreshExternalScenes()
    }

    private func refreshExternalScenes() {
        guard let store else { return }
        let externalScene = UIApplication.shared.connectedScenes
            .compactMap { $0 as? UIWindowScene }
            .first { scene in
                scene.session.role == .windowExternalDisplayNonInteractive
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
        let audienceRoot = ExternalAirPlayAudienceRoot(store: store)
        let host = UIHostingController(rootView: audienceRoot)
        host.view.backgroundColor = .clear
        win.rootViewController = host
        win.isHidden = false
        externalWindow = win
        isExternalDisplayConnected = true
    }
}

/// Root view hosted on an external non-mirrored AirPlay / HDMI display.
private struct ExternalAirPlayAudienceRoot: View {
    @Bindable var store: InfPadStore

    var body: some View {
        ZStack {
            store.theme.paperBackground.ignoresSafeArea()
            if store.activeTab == .slides {
                SlideAudienceView(
                    store: store,
                    slide: SlideDeck.slides[store.currentSlideIndex],
                    interactiveDemoButtons: false,
                    allowAnnotationInput: false
                )
                .padding(24)
            } else {
                // When presenter jumps to live Calculator, mirror clean Lean 4 result / plot on stage
                VStack(spacing: 18) {
                    Text(store.expressionText.isEmpty ? "InfPad · Lean 4 FastLC" : store.expressionText)
                        .font(.system(size: 40, weight: .bold, design: .monospaced))
                        .foregroundStyle(store.theme.primaryInk)
                    if let ev = store.evalResult, ev.ok, let plot = ev.plot, ev.isFunction {
                        FunctionPlotCard(
                            eval: ev,
                            plot: plot,
                            theme: store.theme,
                            currentN: Int(store.sliderN.rounded()),
                            latencyText: store.leanMs.map { String(format: "Lean %.2f ms", $0) }
                        )
                    } else if let exact = store.evalResult?.exact {
                        Text(exact)
                            .font(.system(size: 44, weight: .semibold, design: .monospaced))
                            .foregroundStyle(store.theme.accentCobalt)
                            .multilineTextAlignment(.center)
                            .padding(28)
                            .background(store.theme.elevatedCard, in: RoundedRectangle(cornerRadius: 20, style: .continuous))
                    }
                }
                .padding(36)
            }
        }
        .preferredColorScheme(store.isDark ? .dark : .light)
    }
}
