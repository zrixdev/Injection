THEOS_PACKAGE_SCHEME = rootless
TARGET := iphone:clang:14.5:14.0
ARCHS = arm64

include $(THEOS)/makefiles/common.mk

LIBRARY_NAME = MLBInject
MLBInject_FILES = Inject.mm \
    imgui/imgui.cpp \
    imgui/imgui_draw.cpp \
    imgui/imgui_tables.cpp \
    imgui/imgui_widgets.cpp \
    imgui/backends/imgui_impl_metal.mm
MLBInject_FRAMEWORKS = UIKit Foundation Metal MetalKit QuartzCore
MLBInject_CFLAGS = -Iimgui -Iimgui/backends -std=gnu++17 -fobjc-arc \
    -fno-modules -Wno-error -Wno-deprecated-declarations
MLBInject_CODESIGN_FLAGS = -S

include $(THEOS_MAKE_PATH)/library.mk
