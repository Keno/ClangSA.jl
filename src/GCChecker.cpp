namespace {
    using namespace clang;
    using namespace ento;
  
    class GCPushPopChecker : public Checker<eval::Call,
                                            check::EndFunction,
                                            check::PostCall,
                                            check::PreCall,
                                            check::Bind
                                            > {
        mutable std::unique_ptr<BugType> BT;
        void report_error(CheckerContext &C, const char *message) const;
        void report_value_error(CheckerContext &C, SymbolRef Sym, const char *message) const;
    
    public:
        struct ValueState {
            enum State { Allocated, Rooted, PotentiallyFreed } S;
            const MemRegion *Root;
            ValueState(State InS, const MemRegion *Root) : S(InS), Root(Root) {}
            
            bool operator==(const ValueState &VS) const {
                return S == VS.S && Root == VS.Root;
            }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(S);
                ID.AddPointer(Root);
            }
            
            bool isRooted() const { return S == Rooted; }
            bool isPotentiallyFreed() const { return S == PotentiallyFreed; }
            bool isJustAllocated() const { return S == Allocated; }
            
            bool isRootedBy(const MemRegion *R) const { return isRooted() && R == Root; }
            
            static ValueState getAllocated() { return ValueState(Allocated, nullptr); }
            static ValueState getFreed() { return ValueState(PotentiallyFreed, nullptr); }
            static ValueState getRooted(const MemRegion *Root) { return ValueState(Rooted, Root); }
        };
        
        struct RootState {
            enum State { Root } S;
            unsigned RootedAtDepth;
            
            RootState(State InS, unsigned Depth) : S(InS), RootedAtDepth(Depth) {}
            
            bool operator==(const RootState &VS) const {
                return S == VS.S && RootedAtDepth == VS.RootedAtDepth;
            }
            
            bool shouldPopAtDepth(unsigned Depth) const { return Depth == RootedAtDepth; }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(S);
                ID.AddInteger(RootedAtDepth);
            }
            
            static RootState getRoot(unsigned Depth) { return RootState(Root, Depth); }
        };
        
    private:
        bool isGCTrackedTypeName(StringRef Name) const;
        bool isGCTrackedType(QualType Type) const;
        static void dumpState(const ProgramStateRef &State);
        bool isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const;
        bool isSafepoint(const CallEvent &Call) const;
        bool processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        
    public:
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
        void checkBind(SVal Loc, SVal Val, const Stmt *S, CheckerContext &) const;
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
        
        class GCValueBugVisitor
          : public BugReporterVisitorImpl<GCValueBugVisitor> {
        protected:
          SymbolRef Sym;
            
        public:
          GCValueBugVisitor(SymbolRef S) : Sym(S) {}

          void Profile(llvm::FoldingSetNodeID &ID) const override {
            static int X = 0;
            ID.AddPointer(&X);
            ID.AddPointer(Sym);
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
REGISTER_MAP_WITH_PROGRAMSTATE(GCRootMap, const MemRegion *, GCPushPopChecker::RootState)

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

clang::ento::PathDiagnosticPiece *GCPushPopChecker::GCValueBugVisitor::VisitNode(
  const ExplodedNode *N, const ExplodedNode *PrevN,
  BugReporterContext &BRC, BugReport &BR) {
    const ValueState *NewValueState = N->getState()->get<GCValueMap>(Sym);
    const ValueState *OldValueState = PrevN->getState()->get<GCValueMap>(Sym);
    if (!NewValueState || !OldValueState)
      return nullptr;
    PathDiagnosticLocation Pos(PathDiagnosticLocation::getStmt(N),
                         BRC.getSourceManager(),
                         N->getLocationContext());
    if (NewValueState->isPotentiallyFreed() &&
        OldValueState->isJustAllocated()) {
      // std::make_shared< in later LLVM
      return new PathDiagnosticEventPiece(Pos, "Value may have been GCed here.");
    } else if (NewValueState->isRooted() &&
               OldValueState->isJustAllocated()) {
      return new PathDiagnosticEventPiece(Pos, "Value was rooted here.");      
    } else if (NewValueState->isJustAllocated() &&
               OldValueState->isRooted()) {
      return new PathDiagnosticEventPiece(Pos, "Root was released here.");    
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

void GCPushPopChecker::report_value_error(CheckerContext &C, SymbolRef Sym, const char *message) const
{
    // Generate an error node.
    ExplodedNode *N = C.generateErrorNode();
    if (!N)
      return;
  
    if (!BT)
        BT.reset(new BugType(this, "Invalid GC thingy",
                           categories::LogicError));
    auto Report = llvm::make_unique<BugReport>(*BT, message, N);
    Report->addVisitor(llvm::make_unique<GCValueBugVisitor>(Sym));
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

bool GCPushPopChecker::isSafepoint(const CallEvent &Call) const
{
  bool isCalleeSafepoint = true;
  const FunctionDecl *FD = Call.getDecl()->getAsFunction();
  if (FD) {
      isCalleeSafepoint = !isFDAnnotatedNotSafepoint(FD);
  }
  return isCalleeSafepoint;
}

bool GCPushPopChecker::processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const
{
  if (!isSafepoint(Call))
    return false;
  bool DidChange = false;
  SValExplainer Ex(C.getASTContext());
  // Symbolically free all unrooted values.
  GCValueMapTy AMap = State->get<GCValueMap>();
  for (auto I = AMap.begin(), E = AMap.end(); I != E; ++I) {
      if (I.getData().isJustAllocated()) {
          State = State->set<GCValueMap>(I.getKey(), ValueState::getFreed());
          DidChange = true;
      }
  }
  return DidChange;
}

bool GCPushPopChecker::processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const {
  QualType QT = Call.getResultType();
  if (!isGCTrackedType(QT))
      return false;
  State = State->set<GCValueMap>(Call.getReturnValue().getAsSymbol(), ValueState::getAllocated());
  return true;
}

void GCPushPopChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  bool didChange = processPotentialSafepoint(Call, C, State);
  didChange |= processAllocationOfResult(Call, C, State);
  if (didChange)
    C.addTransition(State);
}

void GCPushPopChecker::dumpState(const ProgramStateRef &State) {
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
    bool isCalleeSafepoint = isSafepoint(Call);
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
            report_value_error(C, Arg.getAsSymbol(), "Argument value may have been GCed");
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
        // Go through all roots, see which ones are no longer with us.
        // The go through the values and unroot those for which those were our
        // roots.
        ProgramStateRef State = C.getState()->set<GCDepth>(CurrentDepth);
        GCRootMapTy AMap = State->get<GCRootMap>();
        SmallVector<const MemRegion *, 5> PoppedRoots;
        for (auto I = AMap.begin(), E = AMap.end(); I != E; ++I) {
            if (I.getData().shouldPopAtDepth(CurrentDepth)) {
                PoppedRoots.push_back(I.getKey());
                State = State->remove<GCRootMap>(I.getKey());
            }
        }
        GCValueMapTy VMap = State->get<GCValueMap>();
        for (const MemRegion *R : PoppedRoots) {
            for (auto I = VMap.begin(), E = VMap.end(); I != E; ++I) {
                if (I.getData().isRootedBy(R)) {
                    State = State->set<GCValueMap>(I.getKey(), ValueState::getAllocated());
                }
            }
        }
        C.addTransition(State);
        return true;
    } else if (name == "JL_GC_PUSH1" ||
               name == "JL_GC_PUSH2" ||
               name == "JL_GC_PUSH3" ||
               name == "JL_GC_PUSH4" ||
               name == "JL_GC_PUSH5") {
        ProgramStateRef State = C.getState();
        // Transform slots to roots, transform values to rooted
        unsigned NumArgs = CE->getNumArgs();
        for (unsigned i = 0; i < NumArgs; ++i) {
            SVal V = C.getSVal(CE->getArg(i));
            auto MRV = V.getAs<loc::MemRegionVal>();
            if (!MRV)
                report_error(C, "JL_GC_PUSH with something other than a local variable");
            const MemRegion *Region = MRV->getRegion();
            State = State->set<GCRootMap>(Region, RootState::getRoot(CurrentDepth));
            // Now for the value
            SVal Value = State->getSVal(Region);
            const ValueState *ValState = State->get<GCValueMap>(Value.getAsSymbol());
            if (!ValState)
              continue;
            if (ValState->isPotentiallyFreed())
              report_value_error(C, Value.getAsSymbol(), "Trying to root value which may have been GCed");
            State = State->set<GCValueMap>(Value.getAsSymbol(), ValueState::getRooted(Region));
        }
        CurrentDepth += 1;
        State = State->set<GCDepth>(CurrentDepth);
        C.addTransition(State); 
        return true;
    } else if (name == "_JL_GC_PUSHARGS" ||
        name == "jl_gc_push_arraylist") {
        CurrentDepth += 1;
        C.addTransition(C.getState()->set<GCDepth>(CurrentDepth));
        return true;
    }
    return false;
}

void GCPushPopChecker::checkBind(SVal LVal, SVal RVal, const clang::Stmt *S, CheckerContext &C) const {
    auto State = C.getState();
    const MemRegion *R = LVal.getAsRegion();
    if (!R)
        return;
    const auto *RootState = State->get<GCRootMap>(R);
    if (!RootState)
        return;
    SymbolRef Sym = RVal.getAsSymbol();
    const auto *RValState = State->get<GCValueMap>(Sym);
    if (!RValState)
        report_error(C, "Saw assignment to root, but missed the allocation");
    if (RValState->isPotentiallyFreed())
        report_value_error(C, Sym, "Trying to root value which may have been GCed");
    C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(R)));
}

void registerGcPushPopChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCPushPopChecker>();
}
