namespace {
    using namespace clang;
    using namespace ento;
  
#if LLVM_VERSION_MAJOR >= 4
    #define PDP std::shared_ptr<PathDiagnosticPiece>
    #define MakePDP llvm::make_unique<PathDiagnosticEventPiece>
#else
    #define PDP clang::ento::PathDiagnosticPiece * 
    #define MakePDP new clang::ento::PathDiagnosticEventPiece
#endif        
  
    class GCPushPopChecker : public Checker<eval::Call,
                                            check::BeginFunction,
                                            check::EndFunction,
                                            check::PostCall,
                                            check::PreCall,
                                            check::PostStmt<CStyleCastExpr>,
                                            check::PostStmt<ArraySubscriptExpr>,
                                            check::PostStmt<MemberExpr>,
                                            check::Bind,
                                            check::Location
                                            > {
        mutable std::unique_ptr<BugType> BT;
        template <typename callback>
        void report_error(callback f, CheckerContext &C, const char *message) const;
        void report_error(CheckerContext &C, const char *message) const {
            return report_error([](BugReport *){}, C, message);
        }
        void report_value_error(CheckerContext &C, SymbolRef Sym, const char *message, clang::SourceRange range = clang::SourceRange()) const;
    
    public:
        struct ValueState {
            enum State { Allocated, Rooted, PotentiallyFreed } S;
            const MemRegion *Root;
            int RootDepth;
            ValueState(State InS, const MemRegion *Root, int Depth) : S(InS), Root(Root), RootDepth(Depth) {}
            
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
            
            static ValueState getAllocated() { return ValueState(Allocated, nullptr, -1); }
            static ValueState getFreed() { return ValueState(PotentiallyFreed, nullptr, -1); }
            static ValueState getRooted(const MemRegion *Root, int Depth) { return ValueState(Rooted, Root, Depth); }
        };
        
        struct RootState {
            enum Kind { Root, RootArray } K;
            int RootedAtDepth;
            
            RootState(Kind InK, int Depth) : K(InK), RootedAtDepth(Depth) {}
            
            bool operator==(const RootState &VS) const {
                return K == VS.K && RootedAtDepth == VS.RootedAtDepth;
            }
            bool operator!=(const RootState &VS) const {
                return K != VS.K || RootedAtDepth != VS.RootedAtDepth;
            }
            
            bool shouldPopAtDepth(int Depth) const { return Depth == RootedAtDepth; }
            bool isRootArray() const { return K == RootArray; }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(K);
                ID.AddInteger(RootedAtDepth);
            }
            
            static RootState getRoot(int Depth) { return RootState(Root, Depth); }
            static RootState getRootArray(int Depth) { return RootState(RootArray, Depth); }
        };
        
    private:
        template <typename callback>
        static bool isJuliaType(callback f, QualType QT) {
          if (!QT->isPointerType() && !QT->isArrayType())
              return false;
          QT = QualType(QT->getPointeeOrArrayElementType(), 0);
          if (QT->isPointerType())
              return isJuliaType(f, QT);
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
        template <typename callback>
        static SymbolRef walkToRoot(callback f, const ProgramStateRef &State, const MemRegion *Region);
        
        bool isGCTrackedType(QualType Type) const;
        bool isGloballyRootedType(QualType Type) const;
        bool isBundleOfGCValues(QualType QT) const;
        static void dumpState(const ProgramStateRef &State);
        static bool declHasAnnotation(const clang::Decl *D, const char *which);
        bool isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) const;
        bool isSafepoint(const CallEvent &Call) const;
        bool processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processArgumentRooting(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool rootRegionIfGlobal(const MemRegion *R, ProgramStateRef &, CheckerContext &C) const;
        static const ValueState *getValStateForRegion(ASTContext &AstC, const ProgramStateRef &State, const MemRegion *R, bool Debug = false);
        bool gcEnabledHere(CheckerContext &C) const;
        bool propagateArgumentRootedness(CheckerContext &C, ProgramStateRef &State) const;
        
    public:
        void checkBeginFunction(CheckerContext &Ctx) const;
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostStmt(const CStyleCastExpr *CE, CheckerContext &C) const;
        void checkPostStmt(const ArraySubscriptExpr *CE, CheckerContext &C) const;
        void checkPostStmt(const MemberExpr *ME, CheckerContext &C) const;
        void checkDerivingExpr(const Expr *Result, const Expr *Parent, CheckerContext &C) const;
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

          PDP VisitNode(const ExplodedNode *N,
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

          PDP ExplainNoPropagation(
              const ExplodedNode *N, PathDiagnosticLocation Pos, BugReporterContext &BRC, BugReport &BR);
          PDP VisitNode(const ExplodedNode *N,
                                                         const ExplodedNode *PrevN,
                                                         BugReporterContext &BRC,
                                                         BugReport &BR) override;
        };
    };
    
}
                
REGISTER_TRAIT_WITH_PROGRAMSTATE(GCDepth, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(GCDisabledAt, unsigned)
REGISTER_MAP_WITH_PROGRAMSTATE(GCValueMap, SymbolRef, GCPushPopChecker::ValueState)
REGISTER_MAP_WITH_PROGRAMSTATE(GCRootMap, const MemRegion *, GCPushPopChecker::RootState)

template <typename callback>
SymbolRef GCPushPopChecker::walkToRoot(callback f, const ProgramStateRef &State, const MemRegion *Region)
{
    if (!Region)
        return nullptr;
    while (true) {
        const SymbolicRegion *SR = Region->getSymbolicBase();
        if (!SR) {
            return nullptr;
        }
        SymbolRef Sym = SR->getSymbol();
        const ValueState *OldVState = State->get<GCValueMap>(Sym);
        if (f(Sym, OldVState)) {
            if (const SymbolRegionValue *SRV = dyn_cast<SymbolRegionValue>(Sym)) {
                Region = SRV->getRegion();
                continue;
            }
            return nullptr;
        }
        return Sym;
    }
}


namespace Helpers {
  static SymbolRef trySuperRegion(SValExplainer &Ex, ProgramStateRef State, SVal Val) {
      const MemRegion *R = Val.getAsRegion();
      const SubRegion *SR = R->getAs<SubRegion>();
      return SR ? State->getSVal(SR->getSuperRegion()).getAsSymbol() : nullptr;
  }
  
  static const VarRegion *walk_back_to_global_VR(const MemRegion *Region) {
    while (true) {
        const VarRegion *VR = Region->getAs<VarRegion>();
        if (VR && VR->getDecl()->hasGlobalStorage()) {
            return VR;
        }
        const SymbolicRegion *SymR = Region->getAs<SymbolicRegion>();
        if (SymR) {
            const SymbolRegionValue *SymRV = dyn_cast<SymbolRegionValue>(SymR->getSymbol());
            if (!SymRV)
                break;
            Region = SymRV->getRegion();
            continue;
        }
        const SubRegion *SR = Region->getAs<SubRegion>();
        if (!SR)
            break;
        Region = SR->getSuperRegion();
    }
    return nullptr;
  }
}

PDP GCPushPopChecker::GCBugVisitor::VisitNode(
  const ExplodedNode *N, const ExplodedNode *PrevN,
  BugReporterContext &BRC, BugReport &BR) {
    unsigned NewGCDepth = N->getState()->get<GCDepth>();
    unsigned OldGCDepth = PrevN->getState()->get<GCDepth>();
    if (NewGCDepth != OldGCDepth) {
      PathDiagnosticLocation Pos(PathDiagnosticLocation::getStmt(N),
                           BRC.getSourceManager(),
                           N->getLocationContext());
      // std::make_shared< in later LLVM
      return MakePDP(Pos, "GC frame changed here.");
    }
    return nullptr;
}

PDP GCPushPopChecker::GCValueBugVisitor::ExplainNoPropagation(
    const ExplodedNode *N, PathDiagnosticLocation Pos, BugReporterContext &BRC, BugReport &BR)
{
    if (N->getLocation().getAs<StmtPoint>()) {
        const clang::Stmt *TheS = N->getLocation().castAs<StmtPoint>().getStmt();
        const clang::CallExpr *CE = dyn_cast<CallExpr>(TheS);
        if (!CE)
            return nullptr;
        const clang::FunctionDecl *FD = CE->getDirectCallee();
        if (!FD)
            return nullptr;
        for (int i = 0; i < FD->getNumParams(); ++i) {
            if (!declHasAnnotation(FD->getParamDecl(i), "julia_propagates_root"))
                continue;
            const MemRegion *Region = N->getState()->getSVal(CE->getArg(i), N->getLocationContext()).getAsRegion();
            SValExplainer Ex(BRC.getASTContext());
            std::cout << "Debug 1 " << Ex.Visit(N->getState()->getSVal(CE->getArg(i), N->getLocationContext())) << std::endl;
            SymbolRef Parent = walkToRoot([](SymbolRef Sym, const ValueState *OldVState) {return !OldVState;},
                N->getState(), Region);
            if (!Parent) {
                // May have been derived from a global. Check that
                const VarRegion *VR = Helpers::walk_back_to_global_VR(Region);
                if (VR) {
                  BR.addNote("Derivation root was here", PathDiagnosticLocation::create(VR->getDecl(), BRC.getSourceManager()));
                  return MakePDP(Pos, "Argument value was derived from global. May need GLOBALLY_ROOTED annotation.");                      
                }
                return MakePDP(Pos, "Could not propagate root. Argument value was untracked.");
            }
            const ValueState *ValS = N->getState()->get<GCValueMap>(Parent);
            assert(ValS);
            if (ValS->isPotentiallyFreed()) {
                BR.addVisitor(llvm::make_unique<GCValueBugVisitor>(Parent));
                return MakePDP(Pos, "Root not propagated because it may have been freed. Tracking.");
            } else {
                BR.addVisitor(llvm::make_unique<GCValueBugVisitor>(Parent));
                return MakePDP(Pos, "No Root to propagate. Tracking.");
            }
        }
        return nullptr;
    }
    return nullptr;
}

PDP GCPushPopChecker::GCValueBugVisitor::VisitNode(
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
        if (NewValueState->isRooted()) {
            return MakePDP(Pos, "Started tracking value here (root was inherited).");            
        } else {
            PDP Diag = ExplainNoPropagation(N, Pos, BRC, BR);
            if (Diag)
                return Diag;
            return MakePDP(Pos, "Started tracking value here.");
        }
    }
    if (NewValueState->isPotentiallyFreed() &&
        OldValueState->isJustAllocated()) {
      // std::make_shared< in later LLVM
      return MakePDP(Pos, "Value may have been GCed here.");
    } else if (NewValueState->isRooted() &&
               OldValueState->isJustAllocated()) {
      return MakePDP(Pos, "Value was rooted here.");      
    } else if (NewValueState->isJustAllocated() &&
               OldValueState->isRooted()) {
      return MakePDP(Pos, "Root was released here.");    
    } else if (NewValueState->RootDepth !=
               OldValueState->RootDepth) {
      return MakePDP(Pos, "Rooting Depth changed here.");
    }
    return nullptr;
}

template <typename callback>
void GCPushPopChecker::report_error(callback f, CheckerContext &C, const char *message) const
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
    f(Report.get());
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
    Report->addVisitor(llvm::make_unique<GCBugVisitor>());
    if (!range.isInvalid()) {
        Report->addRange(range);
    }
    C.emitReport(std::move(Report));
}

bool GCPushPopChecker::gcEnabledHere(CheckerContext &C) const {
    int disabledAt = C.getState()->get<GCDisabledAt>();
    return disabledAt == (unsigned)-1;
}

bool GCPushPopChecker::propagateArgumentRootedness(CheckerContext &C, ProgramStateRef &State) const {
    const auto *LCtx = C.getLocationContext();

    const auto *Site = cast<StackFrameContext>(LCtx)->getCallSite();
    if (!Site)
      return false;

    const auto *FD = dyn_cast<FunctionDecl>(LCtx->getDecl());
    if (!FD)
      return false;

    const auto *CE = dyn_cast<CallExpr>(Site);
    if (!CE)
      return false;
      
    //FD->dump();

    bool Change = false;
    int idx = 0;
    SValExplainer Ex(C.getASTContext());
    for (const auto P : FD->parameters()) {
        if (!isGCTrackedType(P->getType())) {
            continue;
        }
        auto Param = State->getLValue(P, LCtx);
        SymbolRef ParamSym = State->getSVal(Param).getAsSymbol();
        if (!ParamSym) {
            continue;
        }
        if (isGloballyRootedType(P->getType())) {
           State = State->set<GCValueMap>(ParamSym, ValueState::getRooted(nullptr, -1));
           Change = true;
           continue;
        }
        auto Arg = State->getSVal(CE->getArg(idx++), LCtx->getParent());
        SymbolRef ArgSym = walkToRoot([](SymbolRef Sym, const ValueState *OldVState) {return !OldVState;},
            State, Arg.getAsRegion());
        if (!ArgSym) {
            continue;
        }
        const ValueState *ValS = State->get<GCValueMap>(ArgSym);
        if (!ValS) {
            std::cout << "Allocation was " << Ex.Visit(ArgSym) << std::endl;
            report_error([&](BugReport *Report) {
                Report->addNote(
                  "Tried to find root for this parameter in inlined call",
                  PathDiagnosticLocation::create(P, C.getSourceManager()));
            }, C, "Missed allocation of parameter");
            continue;
        }
        State = State->set<GCValueMap>(ParamSym, *ValS);
        Change = true;
    }
    return Change;
}

void GCPushPopChecker::checkBeginFunction(CheckerContext &C) const {
    // Consider top-level argument values rooted, unless an annotation says otherwise
    const auto *LCtx = C.getLocationContext();
    const auto *FD = dyn_cast<FunctionDecl>(LCtx->getDecl());
    if (!FD)
        return;
    ProgramStateRef State = C.getState();
    bool Change = false;
    if (C.inTopFrame()) {
        State = State->set<GCDisabledAt>((unsigned)-1);
        Change = true;
    }
    if (State->get<GCDisabledAt>() == (unsigned)-1) {
        if (declHasAnnotation(FD, "julia_gc_disabled")) {
            State = State->set<GCDisabledAt>(C.getStackFrame()->getIndex());
            Change = true;
        }
    }
    if (!C.inTopFrame()) {
        if (propagateArgumentRootedness(C, State))
            C.addTransition(State);
        return;
    }
    bool isFunctionSafePoint = !isFDAnnotatedNotSafepoint(FD);
    SValExplainer EX(C.getASTContext());
    for (const auto P : FD->parameters()) {
        if (isGCTrackedType(P->getType())) {
            auto Param = State->getLValue(P, LCtx);
            SymbolRef Sym = State->getSVal(Param).getAsSymbol();
            if (isFunctionSafePoint)
                State = State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1));
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
    if (C.getState()->get<GCDisabledAt>() == C.getStackFrame()->getIndex()) {
        C.addTransition(C.getState()->set<GCDisabledAt>((unsigned)-1));
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

bool GCPushPopChecker::isBundleOfGCValues(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      if (Name.endswith_lower("typemap_intersection_env"))
          return true;
      return false;
    }, QT);
}

bool GCPushPopChecker::isGCTrackedType(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      if (Name.endswith_lower("jl_value_t") ||
          Name.endswith_lower("jl_svec_t") ||
          Name.endswith_lower("jl_sym_t") ||
          Name.endswith_lower("jl_expr_t") ||
          Name.endswith_lower("jl_code_info_t") ||
          Name.endswith_lower("jl_array_t") ||
          Name.endswith_lower("jl_method_t") ||
          Name.endswith_lower("jl_method_instance_t") ||
          Name.endswith_lower("jl_tupletype_t") ||
          Name.endswith_lower("jl_datatype_t") ||
          Name.endswith_lower("jl_typemap_entry_t") ||
          Name.endswith_lower("jl_typename_t") ||
          Name.endswith_lower("jl_module_t") ||
          Name.endswith_lower("jl_tupletype_t") ||
          Name.endswith_lower("jl_gc_tracked_buffer_t") ||
          Name.endswith_lower("jl_tls_states_t") ||
          Name.endswith_lower("jl_binding_t") ||          
          // Probably not technically true for these, but let's allow it
          Name.endswith_lower("typemap_intersection_env")
          ) {
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
  if (Call.isGlobalCFunction("malloc") ||
      Call.isGlobalCFunction("memcpy") ||
      Call.isGlobalCFunction("memset") ||
      Call.isGlobalCFunction("memcmp") ||
      Call.isGlobalCFunction("strrchr") ||
      Call.isGlobalCFunction("free")) {
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
        case Builtin::BI__builtin_bswap64:
        case Builtin::BI__builtin_va_end:
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
  if (!gcEnabledHere(C))
    return false;
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



const GCPushPopChecker::ValueState *GCPushPopChecker::getValStateForRegion(ASTContext &AstC, 
        const ProgramStateRef &State, const MemRegion *Region, bool Debug) {
    if (!Region)
        return nullptr;
    SValExplainer Ex(AstC);
    SymbolRef Sym = walkToRoot([&](SymbolRef Sym, const ValueState *OldVState) {
      return !OldVState || !OldVState->isRooted();
    },
        State, Region);
    if (!Sym)
        return nullptr;
    return State->get<GCValueMap>(Sym);
}

bool GCPushPopChecker::processArgumentRooting(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const {
    auto *Decl = Call.getDecl();
    const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
    if (!FD)
        return false;
    const MemRegion *RootingRegion = nullptr;
    SymbolRef RootedSymbol = nullptr;
    for (int i = 0; i < FD->getNumParams(); ++i) {
        if (declHasAnnotation(FD->getParamDecl(i), "julia_rooting_argument")) {
            RootingRegion = Call.getArgSVal(i).getAsRegion();
        } else if (declHasAnnotation(FD->getParamDecl(i), "julia_rooted_argument")) {
            RootedSymbol = Call.getArgSVal(i).getAsSymbol();
        }
    }
    if (!RootingRegion || !RootedSymbol)
        return false;
    SValExplainer Ex(C.getASTContext());
    const ValueState *OldVState = getValStateForRegion(C.getASTContext(), State, RootingRegion);
    if (!OldVState)
        return false;
    State = State->set<GCValueMap>(RootedSymbol, *OldVState);
    return true;
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
      State = State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1));
  else {
      const ValueState *ValS = State->get<GCValueMap>(Sym);
      ValueState NewVState = ValueState::getAllocated();
      if (ValS) {
          // If the call was inlined, we may have accidentally killed the return
          // value above. Revive it here.
          const ValueState *PrevValState = C.getState()->get<GCValueMap>(Sym);
          if (!ValS->isPotentiallyFreed() || (PrevValState && PrevValState->isPotentiallyFreed()))
              return false;
          NewVState = *PrevValState;
      }
      auto *Decl = Call.getDecl();
      const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
      if (!FD)
          return false; 
      if (declHasAnnotation(FD, "julia_globally_rooted")) {
          NewVState = ValueState::getRooted(nullptr, -1);
      } else {  
        for (int i = 0; i < FD->getNumParams(); ++i) {
            if (declHasAnnotation(FD->getParamDecl(i), "julia_propagates_root")) {
                // Walk backwards to find the region that roots this value
                const MemRegion *Region = Call.getArgSVal(i).getAsRegion();
                const ValueState *OldVState = getValStateForRegion(C.getASTContext(), State, Region);
                if (OldVState)
                    NewVState = *OldVState;
                break;
            }
        }
      }
      State = State->set<GCValueMap>(Sym, NewVState);
  }
  return true;
}

void GCPushPopChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  bool didChange = processArgumentRooting(Call, C, State);
  didChange |= processPotentialSafepoint(Call, C, State);
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
    C.addTransition(C.getState()->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1)));
}

void GCPushPopChecker::checkDerivingExpr(const Expr *Result, const Expr *Parent, CheckerContext &C) const
{
    // This is the pointer
    SValExplainer Ex(C.getASTContext());
    auto ValLoc = C.getSVal(Result).getAs<Loc>();
    if (!ValLoc) {
        return;
    }
    SymbolRef OldSym = C.getSVal(Parent).getAsSymbol(true);
    ProgramStateRef State = C.getState();
    const ValueState *OldValS = OldSym ? State->get<GCValueMap>(OldSym) : nullptr;
    SVal Loaded = State->getSVal(*ValLoc);
    if (Loaded.isUnknown()) {
      QualType QT = Result->getType();
      if (OldValS || isGCTrackedType(QT)) {
        Loaded = C.getSValBuilder().conjureSymbolVal(Result, C.getLocationContext(), QT,
                                              C.blockCount());
        State = State->bindLoc(*ValLoc, Loaded, C.getLocationContext());
      }
    }
    SymbolRef NewSym = Loaded.getAsSymbol();
    if (!NewSym) {
        return;
    }
    const MemRegion *Region = C.getSVal(Parent).getAsRegion();
    if (Region) {
      const VarRegion *VR = Helpers::walk_back_to_global_VR(Region);
      if (VR && rootRegionIfGlobal(VR, State, C)) {
          C.addTransition(State->set<GCValueMap>(NewSym, ValueState::getRooted(Region, -1)));
          return;
      }
    }
    if (!OldValS) {
        return;
    }
    if (OldValS->isPotentiallyFreed())
        report_value_error(C, OldSym, "Creating derivative of value that may have been GCed");
    else {
        // NewSym might already have a better root
        const ValueState *NewValS = State->get<GCValueMap>(NewSym);
        if (!NewValS || !NewValS->isRooted())
            C.addTransition(State->set<GCValueMap>(NewSym, *OldValS));
    }
}

// Propagate rootedness through subscript
void GCPushPopChecker::checkPostStmt(const ArraySubscriptExpr *ASE, CheckerContext &C) const
{
    checkDerivingExpr(ASE, ASE->getLHS(), C);
}

void GCPushPopChecker::checkPostStmt(const MemberExpr *ME, CheckerContext &C) const
{
    checkDerivingExpr(ME, ME->getBase(), C);
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
    if (!gcEnabledHere(C))
        return;
    for (unsigned idx = 0; idx < NumArgs; ++idx) {
        SVal Arg = Call.getArgSVal(idx);
        SymbolRef Sym = Arg.getAsSymbol();
        if (!Sym)
            continue;
        auto *ValState = State->get<GCValueMap>(Sym);
        if (!ValState)
            continue;
        SourceRange range;
        if (const Expr *E = Call.getArgExpr(idx))
            range = E->getSourceRange();
        if (ValState->isPotentiallyFreed())
            report_value_error(C, Sym, "Argument value may have been GCed", range);
        if (ValState->isRooted())
            continue;
        bool MaybeUnrooted = false;
        if (FD) {
            if (idx < FD->getNumParams())
                MaybeUnrooted = declHasAnnotation(FD->getParamDecl(idx), "julia_maybe_unrooted");
        }
        if (!MaybeUnrooted && isCalleeSafepoint) {
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
            if (!ValState->isRooted()) {
              State = State->set<GCValueMap>(Sym, ValueState::getRooted(Region, CurrentDepth));
            }
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
        // The Argument array may also be used as a value, so make it rooted
        SymbolRef ArgArraySym = ArgArray.getAsSymbol();
        assert(ArgArraySym);
        State = State->set<GCValueMap>(ArgArraySym, ValueState::getRooted(Region, CurrentDepth));
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
        C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1)));
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
    if (!Sym) {
        return;
    }
    const auto *RValState = State->get<GCValueMap>(Sym);
    if (!RValState) {
        if (rootRegionIfGlobal(Sym->getOriginRegion(), State, C)) {
            C.addTransition(State);
            return;
        }
        report_error(C, "Saw assignment to root, but missed the allocation");
        return;
    }
    if (RValState->isPotentiallyFreed())
        report_value_error(C, Sym, "Trying to root value which may have been GCed");
    if (!RValState->isRooted()) {
        C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(R, State->get<GCDepth>())));
    }
}

bool GCPushPopChecker::rootRegionIfGlobal(const MemRegion *R, ProgramStateRef &State, CheckerContext &C) const {
    if (!R)
        return false;
    SValExplainer Ex(C.getASTContext());
    const VarRegion *VR = R->getAs<VarRegion>();
    if (!VR)
        return false;
    const VarDecl *VD = VR->getDecl();
    assert(VD);
    if (!VD->hasGlobalStorage())
        return false;
    if (!isGCTrackedType(VD->getType()))
        return false;
    bool isGlobalRoot = false;
    if (declHasAnnotation(VD, "julia_globally_rooted") ||
        isGloballyRootedType(VD->getType())) {
        State = State->set<GCRootMap>(R, RootState::getRoot(-1));
        isGlobalRoot = true;
    }
    SVal TheVal = State->getSVal(R);
    SymbolRef Sym = TheVal.getAsSymbol();
    if (Sym) {
        const ValueState *GVState = C.getState()->get<GCValueMap>(Sym);
        if (!GVState)
            State = State->set<GCValueMap>(Sym, isGlobalRoot ? ValueState::getRooted(R, State->get<GCDepth>()) : ValueState::getAllocated());
    }
    return true;
}

void GCPushPopChecker::checkLocation(SVal Loc, bool IsLoad, const Stmt *S, CheckerContext &C) const {
    // If it's just the symbol by itself, let it be. We allow dead pointer to be
    // passed around, so long as they're not accessed. However, we do want to
    // start tracking any globals that may have been accessed.
    ProgramStateRef State = C.getState();
    if (rootRegionIfGlobal(Loc.getAsRegion(), State, C)) {
        C.addTransition(State);
        return;
    }
    SymbolRef SymByItself = Loc.getAsSymbol(false);
    if (SymByItself) {
        return;
    }
    // This will walk backwards until it finds the base symbol
    SymbolRef Sym = Loc.getAsSymbol(true);
    if (!Sym) {
      return;
    }
    const ValueState *VState = State->get<GCValueMap>(Sym);
    if (!VState)
      return;
    if (VState->isPotentiallyFreed()) {
      report_value_error(C, Sym, "Trying to access value which may have been GCed");
    }
}


void registerGcPushPopChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCPushPopChecker>();
}
