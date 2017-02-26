using ClangSA

fixeddb = ClangSA.createFixedCompileDatabase(".", ["cc",
  string("-I", joinpath(JULIA_HOME,"../../src")),
  string("-I", joinpath(JULIA_HOME,"../../src/support")),
  string("-I", joinpath(JULIA_HOME,"../include/julia")),    
  ])

ClangSA.runTool(fixeddb, ["GCPushPop.cpp"], ClangSA.getAnalysisAction(), verify = true)

#ClangSA.runTool(fixeddb, [path], ClangSA.getAnalysisAction())
