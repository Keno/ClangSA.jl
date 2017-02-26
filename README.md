# ClangSA

[![Build Status](https://travis-ci.org/Keno/ClangSA.jl.svg?branch=master)](https://travis-ci.org/Keno/ClangSA.jl)

[![Coverage Status](https://coveralls.io/repos/Keno/ClangSA.jl/badge.svg?branch=master&service=github)](https://coveralls.io/github/Keno/ClangSA.jl?branch=master)

[![codecov.io](http://codecov.io/github/Keno/ClangSA.jl/coverage.svg?branch=master)](http://codecov.io/github/Keno/ClangSA.jl?branch=master)

# How to run on julia

First, create a compilation database. The easiest way to do so is to use the
`intercept-build` that comes with clang:

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

# Development tips

This package is designed for rapid iteration. The package can be `reload`ed, and
rerun by repeating the last line above (though you'll have to re-run `getAnalysisAction` to make sure to
pick up the changed code);
