namespace {
    using namespace clang;
    using namespace ento;
  
    class GCPushPopChecker : public Checker<eval::Call,
                                            check::EndFunction,
                                            check::PostCall,
                                            check::PreCall
                                            > {
        mutable std::unique_ptr<BugType> BT;
        void report_error(CheckerContext &C, const char *message) const;
    
    public:
        struct ValueState {
            enum State { Allocated, Rooted, PotentiallyFreed } S;
            ValueState(State InS) : S(InS) {}
            
            bool operator==(const ValueState &VS) const {
                return S == VS.S;
            }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(S);
            }
            
            bool isRooted() const { return S == Rooted; }
            bool isPotentiallyFreed() const { return S == PotentiallyFreed; }
            
            static ValueState getAllocated() { return ValueState(Allocated); }
        };
        
    private:
        bool isGCTrackedTypeName(StringRef Name) const;
        bool isGCTrackedType(QualType Type) const;
        void dumpState(const ProgramStateRef &State) const;
        bool isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const;
        
    public:
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
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
REGISTER_MAP_WITH_PROGRAMSTATE(GCValueMap, SymbolRef, GCPushPopChecker::ValueState)

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

bool GCPushPopChecker::isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const {
    for (const auto *Ann : FD->specific_attrs<AnnotateAttr>()) {
        if (Ann->getAnnotation() == "julia_not_safepoint")
            return true;
    }
    return false;
}

bool GCPushPopChecker::isGCTrackedTypeName(StringRef Name) const {
    if (Name.endswith_lower("jl_value_t") ||
        Name.endswith_lower("jl_svec_t")) {
        return true;
    }
    return false;
}

bool GCPushPopChecker::isGCTrackedType(QualType QT) const {
    if (!QT->isPointerType())
        return false;
    QT = QT->getPointeeType();
    const TypedefType *TT = QT->getAs<TypedefType>();
    if (TT) {
        if (isGCTrackedTypeName(TT->getDecl()->getName()))
            return true;
    }
    const TagDecl *TD = QT->getUnqualifiedDesugaredType()->getAsTagDecl();
    if (!TD)
        return false;
    return isGCTrackedTypeName(TD->getName());
}

void GCPushPopChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
    QualType QT = Call.getResultType();
    if (!isGCTrackedType(QT))
        return;
    auto State = C.getState();
    auto NewState = State->set<GCValueMap>(Call.getReturnValue().getAsSymbol(), ValueState::getAllocated());
    C.addTransition(NewState);
}

void GCPushPopChecker::dumpState(const ProgramStateRef &State) const {
    GCValueMapTy AMap = State->get<GCValueMap>();
    llvm::raw_ostream &Out = llvm::outs();
    Out << "State: " << "\n";
    for (auto I = AMap.begin(), E = AMap.end(); I != E; ++I) {
        I.getKey()->dumpToStream(Out);
    }
}

void GCPushPopChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {
    unsigned NumArgs = Call.getNumArgs();
    ProgramStateRef State = C.getState();
    bool isCalleeSafepoint = true;
    const FunctionDecl *FD = Call.getDecl()->getAsFunction();
    if (FD) {
        FD->dump();
        isCalleeSafepoint = !isFDAnnotatedNotSafepoint(FD);
    }
    for (unsigned idx = 0; idx < NumArgs; ++idx) {
        SVal Arg = Call.getArgSVal(idx);
        auto *ValState = State->get<GCValueMap>(Arg.getAsSymbol());
        if (!ValState)
            continue;
        if (ValState->isRooted())
            continue;
        if (isCalleeSafepoint)
            report_error(C, "Passing non-rooted value as argument to function that may GC");
        else if (ValState->isPotentiallyFreed())
            report_error(C, "Passing value as argument that may have been GCed");
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
               name == "_JL_GC_PUSHARGS" ||
               name == "jl_gc_push_arraylist") {
        CurrentDepth += 1;
        C.addTransition(C.getState()->set<GCDepth>(CurrentDepth));                    
        return true;
    }
    return false;
}

void registerGcPushPopChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCPushPopChecker>();
}
