namespace {
    using namespace clang;
    using namespace ento;
  
    class GCPushPopChecker : public Checker<eval::Call,
                                            check::EndFunction
                                            > {
        mutable std::unique_ptr<BugType> BT;
        void report_error(CheckerContext &C, const char *message) const;
        
    public:
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        class GCBugVisitor
          : public BugReporterVisitorImpl<GCBugVisitor> {
        public:
          GCBugVisitor() {}

          void Profile(llvm::FoldingSetNodeID &ID) const override {
            static int X = 0;
            ID.AddPointer(&X);
          }

          clang::ento::PathDiagnosticPiece * VisitNode(const ExplodedNode *N,
                                                         const ExplodedNode *PrevN,
                                                         BugReporterContext &BRC,
                                                         BugReport &BR) override;
        };
    };
    
}
                
REGISTER_TRAIT_WITH_PROGRAMSTATE(GCDepth, unsigned)

clang::ento::PathDiagnosticPiece *GCPushPopChecker::GCBugVisitor::VisitNode(
  const ExplodedNode *N, const ExplodedNode *PrevN,
  BugReporterContext &BRC, BugReport &BR) {
    unsigned NewGCDepth = N->getState()->get<GCDepth>();
    unsigned OldGCDepth = PrevN->getState()->get<GCDepth>();
    if (NewGCDepth != OldGCDepth) {
      PathDiagnosticLocation Pos(PathDiagnosticLocation::getStmt(N),
                           BRC.getSourceManager(),
                           N->getLocationContext());
      // std::make_shared< in later LLVM
      return new PathDiagnosticEventPiece(Pos, "GC frame changed here.");
    }
    return nullptr;
}

void GCPushPopChecker::report_error(CheckerContext &C, const char *message) const
{
    // Generate an error node.
    ExplodedNode *N = C.generateErrorNode();
    if (!N)
      return;
  
    if (!BT)
        BT.reset(new BugType(this, "Invalid GC thingy",
                           categories::LogicError));
    auto Report = llvm::make_unique<BugReport>(*BT, message, N);
    Report->addVisitor(llvm::make_unique<GCBugVisitor>());
    C.emitReport(std::move(Report));
}

void GCPushPopChecker::checkEndFunction(CheckerContext &C) const {
    if (!C.inTopFrame())
        return;
    if (C.getState()->get<GCDepth>() > 0) {
        report_error(C, "Non-popped GC frame present at end of function");
    }
}

bool GCPushPopChecker::evalCall(const CallExpr *CE,
                                       CheckerContext &C) const {
    // These checks should have no effect on the surrounding environment
    // (globals should not be invalidated, etc), hence the use of evalCall.
    unsigned CurrentDepth = C.getState()->get<GCDepth>();
    auto name = C.getCalleeName(CE);
    if (name == "JL_GC_POP") {
        if (CurrentDepth == 0) {
            report_error(C, "JL_GC_POP without corresponding push");
            return true;
        }
        CurrentDepth -= 1;
        C.addTransition(C.getState()->set<GCDepth>(CurrentDepth));
        return true;
    } else if (name == "JL_GC_PUSH1" ||
               name == "JL_GC_PUSH2" ||
               name == "JL_GC_PUSH3" ||
               name == "JL_GC_PUSH4" ||
               name == "JL_GC_PUSH5" ||
               name == "_JL_GC_PUSHARGS") {
        CurrentDepth += 1;
        C.addTransition(C.getState()->set<GCDepth>(CurrentDepth));                    
        return true;
    }
    return false;
}

void registerGcPushPopChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCPushPopChecker>();
}
