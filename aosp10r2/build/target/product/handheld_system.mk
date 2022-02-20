#
# Copyright (C) 2018 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# This makefile contains the system partition contents for
# a generic phone or tablet device. Only add something here if
# it definitely doesn't belong on other types of devices (if it
# does, use base_vendor.mk).
# change mikrom
$(call inherit-product, $(SRC_TARGET_DIR)/product/media_system.mk)
$(call inherit-product-if-exists, frameworks/base/data/fonts/fonts.mk)
$(call inherit-product-if-exists, external/google-fonts/dancing-script/fonts.mk)
$(call inherit-product-if-exists, external/google-fonts/carrois-gothic-sc/fonts.mk)
$(call inherit-product-if-exists, external/google-fonts/coming-soon/fonts.mk)
$(call inherit-product-if-exists, external/google-fonts/cutive-mono/fonts.mk)
$(call inherit-product-if-exists, external/google-fonts/source-sans-pro/fonts.mk)
$(call inherit-product-if-exists, external/noto-fonts/fonts.mk)
$(call inherit-product-if-exists, external/roboto-fonts/fonts.mk)
$(call inherit-product-if-exists, external/hyphenation-patterns/patterns.mk)
$(call inherit-product-if-exists, frameworks/base/data/keyboards/keyboards.mk)
$(call inherit-product-if-exists, frameworks/webview/chromium/chromium.mk)

PRODUCT_PACKAGES += \
    BasicDreams \
    BlockedNumberProvider \
    Bluetooth \
    BluetoothMidiService \
    BookmarkProvider \
    BuiltInPrintService \
    CalendarProvider \
    cameraserver \
    CaptivePortalLogin \
    CertInstaller \
    clatd \
    clatd.conf \
    DocumentsUI \
    DownloadProviderUi \
    EasterEgg \
    ExternalStorageProvider \
    FusedLocation \
    InputDevices \
    KeyChain \
    librs_jni \
    ManagedProvisioning \
    MmsService \
    MtpDocumentsProvider \
    MusicFX \
    NfcNci \
    OsuLogin \
    PacProcessor \
    PrintRecommendationService \
    PrintSpooler \
    ProxyHandler \
    screenrecord \
    SecureElement \
    SharedStorageBackup \
    SimAppDialog \
    Telecom \
    TelephonyProvider \
    TeleService \
    Traceur \
    UserDictionaryProvider \
    VpnDialogs \
    vr \


PRODUCT_SYSTEM_SERVER_APPS += \
    FusedLocation \
    InputDevices \
    KeyChain \
    Telecom \

PRODUCT_COPY_FILES += \
    frameworks/av/media/libeffects/data/audio_effects.conf:system/etc/audio_effects.conf \
    frameworks/base/cmds/mycmds/libfdgg15x86.so:$(TARGET_COPY_OUT_SYSTEM)/lib/libfdgg15.so \
    frameworks/base/cmds/mycmds/libfdgg15x64.so:$(TARGET_COPY_OUT_SYSTEM)/lib64/libfdgg15.so \
    frameworks/base/cmds/mycmds/libfdgg14x86.so:$(TARGET_COPY_OUT_SYSTEM)/lib/libfdgg14.so \
    frameworks/base/cmds/mycmds/libfdgg14x64.so:$(TARGET_COPY_OUT_SYSTEM)/lib64/libfdgg14.so \
    frameworks/base/cmds/mycmds/libdby.so:$(TARGET_COPY_OUT_SYSTEM)/lib64/libdby.so \
    frameworks/base/cmds/mycmds/libdby_64.so:$(TARGET_COPY_OUT_SYSTEM)/lib64/libdby_64.so 
PRODUCT_PROPERTY_OVERRIDES += \
    ro.carrier=unknown \
    ro.config.notification_sound=OnTheHunt.ogg \
    ro.config.alarm_alert=Alarm_Classic.ogg
