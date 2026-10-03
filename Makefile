THEOS ?= $(HOME)/theos
TARGET := iphone:clang:14.5:14.0
export THEOS_PACKAGE_SCHEME = rootless

include $(THEOS)/makefiles/common.mk

SUBPROJECTS += MLBInject
include $(THEOS_MAKE_PATH)/aggregate.mk
