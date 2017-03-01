module ClangSA
    using Cxx

    # Avoid C++ side code-reuse when re-loading the package
    tok = join(rand('a':'z', 5))
    hack = """
      #undef JuliaAnalysisAction
      #undef GCPushPopChecker
      #undef GCDepth
      #undef GCDisabledAt
      #undef GCValueMap
      #undef GCValueMapTy
      #undef registerGcPushPopChecker
      #undef GCRootMap
      #undef GCRootMapTy
      #undef Helpers
      #define JuliaAnalysisAction JuliaAnalysisAction$tok
      #define GCPushPopChecker GCPushPopChecker$tok
      #define GCDepth GCDepth$tok
      #define GCDisabledAt GCDisabledAt$tok
      #define GCValueMap GCValueMap$tok
      #define GCValueMapTy GCValueMap$(tok)Ty
      #define GCRootMap GCRootMap$tok
      #define GCRootMapTy GCRootMap$(tok)Ty
      #define Helpers Helpers$(tok)
      #define registerGcPushPopChecker registerGcPushPopChecker$tok
    """
    Cxx.cxxparse(hack)

    cxx"""
        #include "clang/Tooling/Tooling.h"
        #include "clang/Tooling/CompilationDatabase.h"
        #include "clang/Frontend/FrontendActions.h"
        #include "clang/StaticAnalyzer/Frontend/FrontendActions.h"
        #include "clang/StaticAnalyzer/Core/Checker.h"
        #include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
        #include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
        #include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
        #include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
        #include "clang/StaticAnalyzer/Core/BugReporter/CommonBugCategories.h"
        #include "clang/StaticAnalyzer/Frontend/AnalysisConsumer.h"
        #include "clang/StaticAnalyzer/Checkers/SValExplainer.h"
        #include <iostream>
    """
    
    # The analysis
    # N.B.: The use of cxxparse here avoids Clang's include caching
    Cxx.cxxparse(__current_compiler__, readstring(joinpath(dirname(@__FILE__), "GCChecker.cpp")))
    
    # Frontend Action that registers the above analysis action
    cxx"""
    class JuliaAnalysisAction : public ASTFrontendAction {
        AnalysisASTConsumer *TheConsumer;
    protected:
        std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                       StringRef InFile) override;
        void ExecuteAction () override;
    };
    
    std::unique_ptr<ASTConsumer> JuliaAnalysisAction::CreateASTConsumer(
        CompilerInstance &CI, StringRef InFile) {
        auto Consumer = clang::ento::CreateAnalysisConsumer(CI);
        TheConsumer = Consumer.get();
        return Consumer;
    }
    
    namespace clang {
        namespace ento {
            void registerNoReturnFunctionChecker(CheckerManager &mgr);
        }
    }
    void JuliaAnalysisAction::ExecuteAction() {
        registerGcPushPopChecker(TheConsumer->GetCheckerManager());
        registerNoReturnFunctionChecker(TheConsumer->GetCheckerManager());
        return this->ASTFrontendAction::ExecuteAction();
    }
    """

    #=
     = TODO: Custom Frontend action that registers an AnalysisConsumer and adds
     =       the above checker.
     =#

    function loadDatabase(directory)
        icxx"""
            std::string Err;
            auto database = clang::tooling::CompilationDatabase::loadFromDirectory($directory, Err);
            if (!database)
              $:(error(unsafe_string(icxx"return Err;")));
            database.release();
        """
    end
    
    function julia_strings_to_cpp(strings)
        cppstrings = icxx"std::vector<std::string>{};"
        for string in strings
            icxx"$cppstrings.push_back($string);"
        end
        cppstrings
    end
    
    function runTool(database, sources, action; verify = false)
        cxxsources = julia_strings_to_cpp(sources)
        extra_arg1 = "-isystem"
        extra_arg2 = Cxx.getClangHeadersDir()
        failed = icxx"""
            clang::tooling::ClangTool tool(*$database, $cxxsources);
            tool.clearArgumentsAdjusters();
            tool.appendArgumentsAdjuster(clang::tooling::getClangStripOutputAdjuster());
            tool.appendArgumentsAdjuster(
                getInsertArgumentAdjuster($extra_arg2, clang::tooling::ArgumentInsertPosition::BEGIN));
            tool.appendArgumentsAdjuster(
                getInsertArgumentAdjuster($extra_arg1, clang::tooling::ArgumentInsertPosition::BEGIN));
            std::vector<std::string> args{"--analyze","-Xanalyzer","-analyzer-output=text","--analyzer-no-default-checks","-Xanalyzer","-fcolor-diagnostics"};
            tool.appendArgumentsAdjuster(
                getInsertArgumentAdjuster(args, clang::tooling::ArgumentInsertPosition::BEGIN));
            if ($verify) {
                std::vector<std::string> more_args{"-Xanalyzer","-verify"};
                tool.appendArgumentsAdjuster(
                    getInsertArgumentAdjuster(more_args, clang::tooling::ArgumentInsertPosition::END));
            }
            tool.run($action);
        """
        (failed == 1) && error("Processing failed")
    end
    
    function createFixedCompileDatabase(directory, cmd_args)
        args = julia_strings_to_cpp(cmd_args)
        icxx"new clang::tooling::FixedCompilationDatabase($directory,$args);"
    end
    
    function getAnalysisAction()
        icxx"clang::tooling::newFrontendActionFactory<JuliaAnalysisAction>().release();"
    end

end # module
