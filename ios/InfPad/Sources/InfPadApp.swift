import SwiftUI

@main
struct InfPadApp: App {
    @State private var store = InfPadStore()

    var body: some Scene {
        WindowGroup {
            ContentView(store: store)
                .onAppear {
                    ExternalDisplayManager.shared.attach(store: store)
                }
        }
    }
}
