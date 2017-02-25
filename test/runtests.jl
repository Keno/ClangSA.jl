using ClangSA

database = ClangSA.createFixedCompileDatabase(".",
  ["cc", string("-I", joinpath(JULIA_HOME,"../include/julia"))])
ClangSA.runTool(database, ["GCPushPop.cpp"], ClangSA.getAnalysisAction(), verify = true)
