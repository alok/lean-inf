import SwiftUI

struct SettingsSheet: View {
    @Bindable var store: InfPadStore
    @Environment(\.dismiss) private var dismiss

    @State private var tokenInput: String = ""
    @State private var tokenSavedNotice: Bool = false

    private var hasKeychainOverride: Bool {
        KeychainTokenStore.load() != nil
    }

    private var hasBundledToken: Bool {
        !InfAPIClient.bundledToken().isEmpty
    }

    var body: some View {
        NavigationStack {
            Form {
                Section("Server Endpoint") {
                    TextField("API Base URL", text: $store.serverURL)
                        .font(.system(size: 18, design: .monospaced))
                        .textInputAutocapitalization(.never)
                        .autocorrectionDisabled()
                        .keyboardType(.URL)

                    HStack(spacing: 12) {
                        Button("Tailscale Funnel (HTTPS)") {
                            store.serverURL = InfPadPresets.defaultServerURL
                            Task { await store.checkHealth() }
                        }
                        .buttonStyle(.borderedProminent)

                        Button("Simulator Localhost") {
                            store.serverURL = InfPadPresets.simulatorLocalURL
                            Task { await store.checkHealth() }
                        }
                        .buttonStyle(.bordered)
                    }
                    .font(.system(size: 17, weight: .medium, design: .rounded))

                    HStack {
                        Circle()
                            .fill(store.isConnected ? Color.green : Color.red)
                            .frame(width: 12, height: 12)
                        if let h = store.health, h.ok {
                            Text("Connected · Lean \(h.lean ?? "4") · \(String(format: "%.1f", h.pingMs ?? 0)) ms · OCR \(h.ocrConfigured == true ? "Ready" : "Missing")")
                                .font(.system(size: 17, design: .rounded))
                        } else {
                            Text("Disconnected from \(store.serverURL)")
                                .font(.system(size: 17, design: .rounded))
                        }
                        Spacer()
                        Button("Test") {
                            Task { await store.checkHealth() }
                        }
                        .font(.system(size: 17, weight: .semibold, design: .rounded))
                    }
                }

                Section("OCR Authentication (X-InfPad-Token)") {
                    HStack {
                        Text("Active Token Source")
                            .font(.system(size: 18, design: .rounded))
                        Spacer()
                        if hasKeychainOverride {
                            Text("Keychain Override")
                                .font(.system(size: 17, weight: .semibold, design: .rounded))
                                .foregroundStyle(.blue)
                        } else if hasBundledToken {
                            Text("Build Config (Ready)")
                                .font(.system(size: 17, weight: .semibold, design: .rounded))
                                .foregroundStyle(.green)
                        } else {
                            Text("Not Configured")
                                .font(.system(size: 17, weight: .semibold, design: .rounded))
                                .foregroundStyle(.red)
                        }
                    }

                    SecureField("Paste INFPAD_OCR_TOKEN to override…", text: $tokenInput)
                        .font(.system(size: 18, design: .monospaced))
                        .textInputAutocapitalization(.never)
                        .autocorrectionDisabled()

                    HStack(spacing: 12) {
                        Button("Save Override to Keychain") {
                            KeychainTokenStore.save(tokenInput)
                            tokenInput = ""
                            tokenSavedNotice = true
                        }
                        .disabled(tokenInput.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
                        .buttonStyle(.borderedProminent)

                        if hasKeychainOverride {
                            Button("Clear Override", role: .destructive) {
                                KeychainTokenStore.delete()
                                tokenSavedNotice = false
                            }
                            .buttonStyle(.bordered)
                        }
                    }
                    .font(.system(size: 17, weight: .medium, design: .rounded))

                    if tokenSavedNotice {
                        Text("Token saved securely to iOS Keychain.")
                            .font(.system(size: 16, design: .rounded))
                            .foregroundStyle(.green)
                    }
                }

                Section("Lean 4 FastLC Precision & Appearance") {
                    Stepper(value: $store.order, in: 4...24) {
                        Text("Series Truncation Order: \(store.order)")
                            .font(.system(size: 18, design: .rounded))
                    }
                    .onChange(of: store.order) { _, _ in
                        Task { await store.evaluateExpression(store.expressionText, saveToHistory: false) }
                    }

                    Toggle(isOn: $store.isDark) {
                        Text("Soft Slate Dark Mode (Default: Warm Paper)")
                            .font(.system(size: 18, design: .rounded))
                    }
                }

                Section("History") {
                    Button("Clear Saved History (\(store.history.count))", role: .destructive) {
                        store.clearHistory()
                    }
                    .font(.system(size: 18, design: .rounded))
                    .disabled(store.history.isEmpty)
                }
            }
            .navigationTitle("InfPad Settings")
            .toolbar {
                ToolbarItem(placement: .confirmationAction) {
                    Button("Done") { dismiss() }
                        .font(.system(size: 18, weight: .semibold, design: .rounded))
                }
            }
        }
    }
}
