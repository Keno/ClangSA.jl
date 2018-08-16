# ClangSA

[![Build Status](https://travis-ci.org/Keno/ClangSA.jl.svg?branch=master)](https://travis-ci.org/Keno/ClangSA.jl)

[![Coverage Status](https://coveralls.io/repos/Keno/ClangSA.jl/badge.svg?branch=master&service=github)](https://coveralls.io/github/Keno/ClangSA.jl?branch=master)

[![codecov.io](http://codecov.io/github/Keno/ClangSA.jl/coverage.svg?branch=master)](http://codecov.io/github/Keno/ClangSA.jl?branch=master)

# How to run on julia

First, create a compilation database. The easiest way to do so is to use the
`intercept-build` that comes with clang (in clang/tools/scan-build-py/bin):

```
cd julia
make clean
intercept-build make -j4
```

This should have created a `compile_commands.json` file. Then, from julia, run:
```
srcdir = joinpath(JULIA_HOME, "../../src"))
paths = filter(path->(endswith(path,".c") || endswith(path,".cpp")),
  readdir(srcdir)
database = ClangSA.loadDatabase(srcdir)
ClangSA.runTool(database, map(p->joinpath(srcdir, p), paths), ClangSA.getAnalysisAction())
```

# Building as part of an LLVM build

Simply symlink the GCChecker.cpp file from this package's `src/` directory into `clang/lib/StaticAnalyzer/Checkers`
and add it to the CMakeLists.txt file in the same directory. You can then run
`clang-check -extra-arg="-Xanalyzer" -extra-arg="-analyzer-checker=julia.GCChecker" -extra-arg -Xclang -extra-arg -analyzer-output=text -analyze src/*{.c,.cpp}`

You will also need to add the following at the end of include/clang/StaticAnalyzer/Checkers/Checkers.td:
```
 //===----------------------------------------------------------------------===//
 // Julia Checkers
 //===----------------------------------------------------------------------===//
 def Julia : Package<"julia">;
 let ParentPackage = Julia in {

 def GCChecker : Checker<"GCChecker">,
    HelpText<"Checks invariants of the Julia GC API.">,
    DescFile<"GCChecker.cpp">;
 } // end "julia"
 ```

# Development tips

This package is designed for rapid iteration. The package can be `reload`ed, and
rerun by repeating the last line above (though you'll have to re-run `getAnalysisAction` to make sure to
pick up the changed code);
