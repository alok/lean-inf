import Foundation
import Security

enum InfAPIError: LocalizedError {
    case invalidURL
    case httpError(Int, String)
    case missingToken
    case network(String)

    var errorDescription: String? {
        switch self {
        case .invalidURL:
            return "Invalid server URL. Check Settings."
        case .httpError(let code, let message):
            if code == 401 {
                return "OCR auth rejected (401). Set the matching INFPAD_OCR_TOKEN in Settings."
            }
            return "Server HTTP \(code): \(message)"
        case .missingToken:
            return "OCR token not configured. Enter INFPAD_OCR_TOKEN in Settings or Secrets.xcconfig."
        case .network(let msg):
            return msg
        }
    }
}

enum KeychainTokenStore {
    private static let service = "com.alok.InfPad"
    private static let account = "INFPAD_OCR_TOKEN"

    static func load() -> String? {
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
            kSecReturnData as String: true,
            kSecMatchLimit as String: kSecMatchLimitOne,
        ]
        var result: AnyObject?
        let status = SecItemCopyMatching(query as CFDictionary, &result)
        guard status == errSecSuccess, let data = result as? Data,
              let value = String(data: data, encoding: .utf8), !value.isEmpty else {
            return nil
        }
        return value
    }

    static func save(_ token: String) {
        let trimmed = token.trimmingCharacters(in: .whitespacesAndNewlines)
        delete()
        guard !trimmed.isEmpty, let data = trimmed.data(using: .utf8) else { return }
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
            kSecValueData as String: data,
            kSecAttrAccessible as String: kSecAttrAccessibleAfterFirstUnlock,
        ]
        SecItemAdd(query as CFDictionary, nil)
    }

    static func delete() {
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
        ]
        SecItemDelete(query as CFDictionary)
    }
}

final class InfAPIClient {
    private let session: URLSession

    /// Allowed characters for a single query parameter value (explicitly excludes `+`, `&`, `=`, `#`, `%`, space).
    private static let strictQueryValueAllowed: CharacterSet = {
        var set = CharacterSet.alphanumerics
        set.insert(charactersIn: "-._~")
        return set
    }()

    init() {
        let config = URLSessionConfiguration.default
        config.timeoutIntervalForRequest = 20
        config.timeoutIntervalForResource = 30
        config.waitsForConnectivity = false
        self.session = URLSession(configuration: config)
    }

    static func bundledToken() -> String {
        let raw = (Bundle.main.object(forInfoDictionaryKey: "INFPAD_OCR_TOKEN") as? String) ?? ""
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed.hasPrefix("$(") { return "" }
        return trimmed
    }

    static func resolvedToken() -> String {
        if let override = KeychainTokenStore.load(), !override.isEmpty {
            return override
        }
        return bundledToken()
    }

    private func normalizedBase(_ raw: String) -> String {
        var s = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        while s.hasSuffix("/") { s.removeLast() }
        return s
    }

    private func encodeQueryValue(_ value: String) -> String {
        value.addingPercentEncoding(withAllowedCharacters: Self.strictQueryValueAllowed) ?? value
    }

    func health(baseURL: String) async throws -> HealthResponse {
        let base = normalizedBase(baseURL)
        guard let url = URL(string: "\(base)/health") else { throw InfAPIError.invalidURL }
        let (data, response) = try await session.data(from: url)
        try validateHTTP(response, data: data)
        return try JSONDecoder().decode(HealthResponse.self, from: data)
    }

    func evaluate(baseURL: String, expr: String, bigN: Double = 100, order: Int = 10) async throws -> EvalResponse {
        let base = normalizedBase(baseURL)
        let nVal = Int(max(1, bigN.rounded()))
        let encodedExpr = encodeQueryValue(expr)
        guard let url = URL(string: "\(base)/eval?expr=\(encodedExpr)&N=\(nVal)&order=\(order)") else {
            throw InfAPIError.invalidURL
        }
        let (data, response) = try await session.data(from: url)
        if let http = response as? HTTPURLResponse, http.statusCode >= 500 {
            let msg = parseServerError(data) ?? "Internal server error"
            throw InfAPIError.httpError(http.statusCode, msg)
        }
        return try JSONDecoder().decode(EvalResponse.self, from: data)
    }

    func ocrEvaluate(
        baseURL: String,
        pngData: Data,
        bigN: Double = 100,
        order: Int = 10
    ) async throws -> OcrEvalResponse {
        let token = Self.resolvedToken()
        guard !token.isEmpty else { throw InfAPIError.missingToken }

        let base = normalizedBase(baseURL)
        guard let url = URL(string: "\(base)/ocr-eval") else { throw InfAPIError.invalidURL }

        struct Payload: Encodable {
            let imageBase64: String
            let mimeType: String
            let N: Int
            let order: Int
        }

        let body = Payload(
            imageBase64: pngData.base64EncodedString(),
            mimeType: "image/png",
            N: Int(max(1, bigN.rounded())),
            order: order
        )

        var req = URLRequest(url: url)
        req.httpMethod = "POST"
        req.setValue("application/json", forHTTPHeaderField: "Content-Type")
        req.setValue(token, forHTTPHeaderField: "X-InfPad-Token")
        req.httpBody = try JSONEncoder().encode(body)

        let (data, response) = try await session.data(for: req)
        try validateHTTP(response, data: data)
        return try JSONDecoder().decode(OcrEvalResponse.self, from: data)
    }

    private func validateHTTP(_ response: URLResponse, data: Data) throws {
        guard let http = response as? HTTPURLResponse else { return }
        guard (200...299).contains(http.statusCode) else {
            let msg = parseServerError(data) ?? HTTPURLResponse.localizedString(forStatusCode: http.statusCode)
            throw InfAPIError.httpError(http.statusCode, msg)
        }
    }

    private func parseServerError(_ data: Data) -> String? {
        struct ErrBody: Decodable { let error: String? }
        if let decoded = try? JSONDecoder().decode(ErrBody.self, from: data), let err = decoded.error {
            return err
        }
        return String(data: data, encoding: .utf8).map { String($0.prefix(200)) }
    }
}
