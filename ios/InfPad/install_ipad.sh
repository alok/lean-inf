#!/bin/bash
# Builds InfPad (Release, signed arm64) and installs + launches it on a connected iPad (e.g. albert (3)).
set -euo pipefail
export PATH=/opt/homebrew/bin:/usr/local/bin:$PATH
cd "$(dirname "$0")"
mkdir -p build

if [ ! -f Secrets.xcconfig ]; then
  echo "Warning: Secrets.xcconfig not found. Copy Secrets.xcconfig.example -> Secrets.xcconfig and set INFPAD_OCR_TOKEN, or enter the token in InfPad Settings."
fi

UDID="${IPAD_UDID:-$(xcrun devicectl list devices 2>/dev/null | grep -i "ipad" | grep -iv "simulat" | grep -Eo '[0-9A-F]{8}-[0-9A-F]{16}' | head -1 || true)}"
if [ -z "$UDID" ]; then
  echo "No physical iPad found. Unlock your iPad on Wi-Fi or connect via USB-C, then re-run."
  xcrun devicectl list devices 2>/dev/null | grep -iv simulat | tail -n +3 || true
  exit 1
fi
echo "Building and installing InfPad on iPad $UDID..."

xcodegen generate --quiet
xcodebuild -project InfPad.xcodeproj -scheme InfPad -configuration Release \
  -destination "id=$UDID" -derivedDataPath build/dd-device \
  -allowProvisioningUpdates -allowProvisioningDeviceRegistration build > build/device.log 2>&1 || {
    grep -E "error:|BUILD (SUCCEEDED|FAILED)" build/device.log | sort -u | head -30
    exit 1
  }
grep -E "BUILD SUCCEEDED" build/device.log | tail -1

xcrun devicectl device install app --device "$UDID" build/dd-device/Build/Products/Release-iphoneos/InfPad.app
xcrun devicectl device process launch --device "$UDID" com.alok.InfPad
echo "InfPad launched on $UDID."
