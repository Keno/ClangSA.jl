namespace {
    using namespace clang;
    using namespace ento;
  
    class GCPushPopChecker : public Checker<eval::Call,
                                            check::BeginFunction,
                                            check::EndFunction,
                                            check::PostCall,
                                            check::PreCall,
                                            check::PostStmt<CStyleCastExpr>,
                                            check::Bind,
                                            check::Location
                                            > {
        mutable std::unique_ptr<BugType> BT;
        void report_error(CheckerContext &C, const char *message) const;
        void report_value_error(CheckerContext &C, SymbolRef Sym, const char *message, clang::SourceRange range = clang::SourceRange()) const;
    
    public:
        struct ValueState {
            enum State { Allocated, Rooted, PotentiallyFreed } S;
            const MemRegion *Root;
            ValueState(State InS, const MemRegion *Root) : S(InS), Root(Root) {}
            
            bool operator==(const ValueState &VS) const {
                return S == VS.S && Root == VS.Root;
            }
            bool operator!=(const ValueState &VS) const {
                return S != VS.S || Root != VS.Root;
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
            enum Kind { Root, RootArray } K;
            unsigned RootedAtDepth;
            
            RootState(Kind InK, unsigned Depth) : K(InK), RootedAtDepth(Depth) {}
            
            bool operator==(const RootState &VS) const {
                return K == VS.K && RootedAtDepth == VS.RootedAtDepth;
            }
            bool operator!=(const RootState &VS) const {
                return K != VS.K || RootedAtDepth != VS.RootedAtDepth;
            }
            
            bool shouldPopAtDepth(unsigned Depth) const { return Depth == RootedAtDepth; }
            bool isRootArray() const { return K == RootArray; }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(K);
                ID.AddInteger(RootedAtDepth);
            }
            
            static RootState getRoot(unsigned Depth) { return RootState(Root, Depth); }
            static RootState getRootArray(unsigned Depth) { return RootState(RootArray, Depth); }
        };
        
    private:
        template <typename callback>
        static bool isJuliaType(callback f, QualType QT) {
          if (!QT->isPointerType())
              return false;
          QT = QT->getPointeeType();
          const TypedefType *TT = QT->getAs<TypedefType>();
          if (TT) {
              if (f(TT->getDecl()->getName()))
                  return true;
          }
          const TagDecl *TD = QT->getUnqualifiedDesugaredType()->getAsTagDecl();
          if (!TD) {
              return false;
          }
          return f(TD->getName());
        }
        bool isGCTrackedType(QualType Type) const;
        bool isGloballyRootedType(QualType Type) const;
        static void dumpState(const ProgramStateRef &State);
        static bool declHasAnnotation(const clang::Decl *D, const char *which);
        bool isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const;
        bool isSafepoint(const CallEvent &Call) const;
        bool processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool rootIfGlobal(SymbolRef SymByItself, CheckerContext &C) const;
        
    public:
        void checkBeginFunction(CheckerContext &Ctx) const;
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostStmt(const CStyleCastExpr *CE, CheckerContext &C) const;
        void checkBind(SVal Loc, SVal Val, const Stmt *S, CheckerContext &) const;
        void checkLocation(SVal Loc, bool IsLoad, const Stmt *S, CheckerContext &) const;
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
    const Stmt *Stmt = PathDiagnosticLocation::getStmt(N);
    
    PathDiagnosticLocation Pos;
    if (Stmt)
      Pos = PathDiagnosticLocation{Stmt,
                           BRC.getSourceManager(),
                           N->getLocationContext()};
    else
      Pos = PathDiagnosticLocation::createDeclEnd(N->getLocationContext(),
                                                  BRC.getSourceManager());
    if (!NewValueState)
      return nullptr;
    if (!OldValueState) {
      return new PathDiagnosticEventPiece(Pos, "Started tracking value here.");
    }
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

void GCPushPopChecker::report_value_error(CheckerContext &C, SymbolRef Sym, const char *message, SourceRange range) const
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
    if (!range.isInvalid()) {
        Report->addRange(range);
    }
    C.emitReport(std::move(Report));
}

// Consider argument values rooted, unless an annotation says otherwise
void GCPushPopChecker::checkBeginFunction(CheckerContext &C) const {
    if (!C.inTopFrame())
        return;
    const auto *LCtx = C.getLocationContext();
    const auto *FD = dyn_cast<FunctionDecl>(LCtx->getDecl());
    if (!FD)
        return;
    bool Change = false;
    bool isFunctionSafePoint = !isFDAnnotatedNotSafepoint(FD);
    ProgramStateRef State = C.getState();
    SValExplainer EX(C.getASTContext());
    for (const auto P : FD->parameters()) {
        if (isGCTrackedType(P->getType())) {
            auto Param = State->getLValue(P, LCtx);
            SymbolRef Sym = State->getSVal(Param).getAsSymbol();
            if (isFunctionSafePoint)
                State = State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr));            
            else
                State = State->set<GCValueMap>(Sym, ValueState::getAllocated());
            Change = true;
        }
    }
    if (Change) {
        C.addTransition(State);
    }
}

void GCPushPopChecker::checkEndFunction(CheckerContext &C) const {
    if (!C.inTopFrame())
        return;
    if (C.getState()->get<GCDepth>() > 0) {
        report_error(C, "Non-popped GC frame present at end of function");
    }
}

bool GCPushPopChecker::declHasAnnotation(const clang::Decl *D, const char *which) {
  for (const auto *Ann : D->specific_attrs<AnnotateAttr>()) {
      if (Ann->getAnnotation() == which)
          return true;
  }
  return false;
}

bool GCPushPopChecker::isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const {
    return declHasAnnotation(FD, "julia_not_safepoint");
}

bool GCPushPopChecker::isGCTrackedType(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      if (Name.endswith_lower("jl_value_t") ||
          Name.endswith_lower("jl_svec_t") ||
          Name.endswith_lower("jl_sym_t") ||
          Name.endswith_lower("jl_expr_t") ||
          Name.endswith_lower("jl_code_info_t") ||
          Name.endswith_lower("jl_array_t")) {
          return true;
      }
      return false; 
    }, QT);
}

bool GCPushPopChecker::isGloballyRootedType(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      return Name.endswith_lower("jl_sym_t");
    }, QT);
}

bool GCPushPopChecker::isSafepoint(const CallEvent &Call) const
{
  bool isCalleeSafepoint = true;
  if (Call.isGlobalCFunction("malloc")) {
    isCalleeSafepoint = false;
  } else {
    auto *Decl = Call.getDecl();
    const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
    if (FD) {
      switch (FD->getBuiltinID()) {
        default:
          isCalleeSafepoint = !isFDAnnotatedNotSafepoint(FD);
          break;

        case Builtin::BI__builtin_expect:
        case Builtin::BI__builtin_alloca:
          isCalleeSafepoint = false;
      }
    }
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
  SymbolRef Sym = Call.getReturnValue().getAsSymbol();
  SValExplainer Ex(C.getASTContext());
  if (!Sym)
      return false;
  if (isGloballyRootedType(QT))
      State = State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr));
  else {
      ValueState NewVState = ValueState::getAllocated();
      auto *Decl = Call.getDecl();
      const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
      if (FD) {
          for (int i = 0; i < FD->getNumParams(); ++i) {
              if (declHasAnnotation(FD->getParamDecl(i), "julia_propagates_root")) {
                  // Walk backwards to find the region that roots this value
                  const MemRegion *Region = Call.getArgSVal(i).getAsRegion();
                  if (!Region)
                    break;
                  while (true) {
                      const SymbolicRegion *SR = Region->getSymbolicBase();
                      if (!SR) {
                        break;
                      }
                      SymbolRef Sym = SR->getSymbol();
                      const ValueState *OldVState = State->get<GCValueMap>(Sym);
                      if (!OldVState || !OldVState->isRooted()) {
                          if (const SymbolRegionValue *SRV = dyn_cast<SymbolRegionValue>(Sym)) {
                              Region = SRV->getRegion();
                              continue;
                          }
                          break;
                      }
                      NewVState = *OldVState;
                      break;                      
                  }
              }
          }
      }
      State = State->set<GCValueMap>(Sym, NewVState);
  }
  return true;
}

void GCPushPopChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  bool didChange = processPotentialSafepoint(Call, C, State);
  didChange |= processAllocationOfResult(Call, C, State);
  if (didChange)
    C.addTransition(State);
}

// Implicitly root values that were casted to globally rooted values
void GCPushPopChecker::checkPostStmt(const CStyleCastExpr *CE, CheckerContext &C) const {
    if (!isGloballyRootedType(CE->getTypeAsWritten()))
        return;
    SymbolRef Sym = C.getSVal(CE).getAsSymbol();
    if (!Sym)
        return;
    C.addTransition(C.getState()->set<GCValueMap>(Sym, ValueState::getRooted(nullptr)));
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
    auto *Decl = Call.getDecl();
    const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
    for (unsigned idx = 0; idx < NumArgs; ++idx) {
        SVal Arg = Call.getArgSVal(idx);
        SymbolRef Sym = Arg.getAsSymbol();
        if (!Sym)
            continue;
        auto *ValState = State->get<GCValueMap>(Sym);
        if (!ValState)
            continue;
        if (ValState->isPotentiallyFreed())
            report_value_error(C, Sym, "Argument value may have been GCed");
        if (ValState->isRooted())
            continue;
        bool MaybeUnrooted = false;
        if (FD) {
            MaybeUnrooted = declHasAnnotation(FD->getParamDecl(idx), "julia_maybe_unrooted");
        }
        if (!MaybeUnrooted && isCalleeSafepoint) {
            SValExplainer Ex(C.getASTContext());
            SourceRange range;
            if (const Expr *E = Call.getArgExpr(idx))
                range = E->getSourceRange();
            report_value_error(C, Sym, "Passing non-rooted value as argument to function that may GC", range);
        }
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
            if (!MRV) {
                report_error(C, "JL_GC_PUSH with something other than a local variable");
                return true;
            }
            const MemRegion *Region = MRV->getRegion();
            State = State->set<GCRootMap>(Region, RootState::getRoot(CurrentDepth));
            // Now for the value
            SVal Value = State->getSVal(Region);
            SymbolRef Sym = Value.getAsSymbol();
            if (!Sym)
              continue;
            const ValueState *ValState = State->get<GCValueMap>(Sym);
            if (!ValState)
              continue;
            if (ValState->isPotentiallyFreed())
              report_value_error(C, Sym, "Trying to root value which may have been GCed");
            State = State->set<GCValueMap>(Sym, ValueState::getRooted(Region));
        }
        CurrentDepth += 1;
        State = State->set<GCDepth>(CurrentDepth);
        C.addTransition(State); 
        return true;
    } else if (name == "_JL_GC_PUSHARGS") {
        ProgramStateRef State = C.getState();
        SVal ArgArray = C.getSVal(CE->getArg(0));
        auto MRV = ArgArray.getAs<loc::MemRegionVal>();
        if (!MRV) {
            report_error(C, "JL_GC_PUSH with something other than an args array");
            return true;
        }
        const MemRegion *Region = MRV->getRegion()->StripCasts();
        SValExplainer Ex(C.getASTContext());
        State = State->set<GCRootMap>(Region, RootState::getRootArray(CurrentDepth));
        CurrentDepth += 1;
        State = State->set<GCDepth>(CurrentDepth);
        C.addTransition(State);
        return true; 
    } else if (name == "jl_gc_push_arraylist") {
        CurrentDepth += 1;
        C.addTransition(C.getState()->set<GCDepth>(CurrentDepth));
        return true;
    } else if (name == "jl_ast_preserve") {
        // TODO: Maybe bind the rooting to the context. For now, the second
        //       argument gets unconditionally rooted
        ProgramStateRef State = C.getState();
        SymbolRef Sym = C.getSVal(CE->getArg(1)).getAsSymbol();
        if (!Sym)
          return true;
        C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr)));
        return true;
    }
    return false;
}

void GCPushPopChecker::checkBind(SVal LVal, SVal RVal, const clang::Stmt *S, CheckerContext &C) const {
    auto State = C.getState();
    const MemRegion *R = LVal.getAsRegion();
    SValExplainer Ex(C.getASTContext());
    if (!R)
        return;
    bool shouldBeRootArray = false;
    const ElementRegion *ER = R->getAs<ElementRegion>();
    if (ER) {
        R = R->getBaseRegion()->StripCasts();
        shouldBeRootArray = true;
    } 
    const auto *RootState = State->get<GCRootMap>(R);
    if (!RootState)
        return;
    if (shouldBeRootArray && !RootState->isRootArray()) {
        report_error(C, "This assignment looks weird. Expected a root array on the LHS.");
        return;
    }
    SymbolRef Sym = RVal.getAsSymbol();
    const auto *RValState = State->get<GCValueMap>(Sym);
    if (!RValState) {
        if (rootIfGlobal(Sym, C))
            return;
        report_error(C, "Saw assignment to root, but missed the allocation");
        return;
    }
    if (RValState->isPotentiallyFreed())
        report_value_error(C, Sym, "Trying to root value which may have been GCed");
    C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(R)));
}

bool GCPushPopChecker::rootIfGlobal(SymbolRef SymByItself, CheckerContext &C) const {
    const MemRegion *R = SymByItself->getOriginRegion();
    if (!R)
        return false;
    const VarRegion *VR = R->getAs<VarRegion>();
    if (!VR)
        return false;
    const VarDecl *VD = VR->getDecl();
    if (!VD->hasGlobalStorage())
        return false;
    if (!isGCTrackedType(VD->getType()))
        return false;
    const ValueState *GVState = C.getState()->get<GCValueMap>(SymByItself);
    if (GVState)
      return false;
    C.addTransition(C.getState()->set<GCValueMap>(SymByItself,
        (declHasAnnotation(VD, "julia_globally_rooted") ||
        isGloballyRootedType(VD->getType())) ?
        ValueState::getRooted(nullptr) : ValueState::getAllocated()));
    return true;
}

void GCPushPopChecker::checkLocation(SVal Loc, bool IsLoad, const Stmt *S, CheckerContext &C) const {
    // If it's just the symbol by itself, let it be. We allow dead pointer to be
    // passed around, so long as they're not accessed. However, we do want to
    // start tracking any globals that may have been accessed.
    SymbolRef SymByItself = Loc.getAsSymbol(false);
    SValExplainer Ex(C.getASTContext());
    if (SymByItself) {
      rootIfGlobal(SymByItself, C);
      return;
    }
    // This will walk backwards until it finds the base symbol
    SymbolRef Sym = Loc.getAsSymbol(true);
    if (!Sym)
      return;
    const ValueState *VState = C.getState()->get<GCValueMap>(Sym);
    if (!VState)
      return;
    if (VState->isPotentiallyFreed()) {
      report_value_error(C, Sym, "Trying to access value which may have been GCed");
    }
}


void registerGcPushPopChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCPushPopChecker>();
}
