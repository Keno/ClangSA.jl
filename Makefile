ifeq ($(LLVM_SRC_DIR),)
$(error "LLVM_SRC_DIR not set")
endif
ifeq ($(LLVM_BIN_DIR),)
$(error "LLVM_BIN_DIR not set")
endif
libGCCheckerPlugin.so: src/GCChecker.cpp
		$(CC) -g -shared -fno-rtti -fPIC -o libGCCheckerPlugin.so -std=c++11 -DCLANG_PLUGIN -I$(LLVM_BIN_DIR)/include -I$(LLVM_BIN_DIR)/tools/clang/include -I$(LLVM_SRC_DIR)/tools/clang/include -I$(LLVM_SRC_DIR)/include -L$(LLVM_BIN_DIR)/lib $< -lclangAnalysis -lclangStaticAnalyzerCore -lclangASTMatchers -lclangAST -lclangLex -lclangBasic
test: libGCCheckerPlugin.so
	PATH=$$PATH:$(LLVM_BIN_DIR)/bin $(LLVM_SRC_DIR)/utils/lit/lit.py -v test
.PHONY: test
