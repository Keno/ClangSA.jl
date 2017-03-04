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
  
    class GCChecker : public Checker<eval::Call,
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
            enum State { Allocated, Rooted, PotentiallyFreed, Untracked } S;
            const MemRegion *Root;
            int RootDepth;
            ValueState(State InS, const MemRegion *Root, int Depth) : S(InS), Root(Root), RootDepth(Depth) {}
            
            bool operator==(const ValueState &VS) const {
                return S == VS.S && Root == VS.Root && RootDepth == VS.RootDepth;
            }
            bool operator!=(const ValueState &VS) const {
                return S != VS.S || Root != VS.Root || RootDepth != VS.RootDepth;
            }
            
            void Profile(llvm::FoldingSetNodeID &ID) const {
                ID.AddInteger(S);
                ID.AddPointer(Root);
                ID.AddInteger(RootDepth);
            }
            
            bool isRooted() const { return S == Rooted; }
            bool isPotentiallyFreed() const { return S == PotentiallyFreed; }
            bool isJustAllocated() const { return S == Allocated; }
            bool isUntracked() const { return S == Untracked; }
            
            bool isRootedBy(const MemRegion *R) const { return isRooted() && R == Root; }
            
            static ValueState getAllocated() { return ValueState(Allocated, nullptr, -1); }
            static ValueState getFreed() { return ValueState(PotentiallyFreed, nullptr, -1); }
            static ValueState getUntracked() { return ValueState(Untracked, nullptr, -1); }
            static ValueState getRooted(const MemRegion *Root, int Depth) { return ValueState(Rooted, Root, Depth); }
            static ValueState getForArgument(const FunctionDecl *FD,
                                             const ParmVarDecl *PVD) {
               bool isFunctionSafepoint = !isFDAnnotatedNotSafepoint(FD);
               bool maybeUnrooted = declHasAnnotation(PVD, "julia_maybe_unrooted");
               if (!isFunctionSafepoint || maybeUnrooted)
                  return getAllocated();
               return getRooted(nullptr, -1);
            }
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
          if (QT->isPointerType() || QT->isArrayType())
              return isJuliaType(f, clang::QualType(QT->getPointeeOrArrayElementType(),0));
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
        
        static bool isGCTrackedType(QualType Type);
        bool isGloballyRootedType(QualType Type) const;
        bool isBundleOfGCValues(QualType QT) const;
        static void dumpState(const ProgramStateRef &State);
        static bool declHasAnnotation(const clang::Decl *D, const char *which);
        static bool isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD);
        bool isSafepoint(const CallEvent &Call) const;
        bool processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool processArgumentRooting(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const;
        bool rootRegionIfGlobal(const MemRegion *R, ProgramStateRef &, CheckerContext &C) const;
        static const ValueState *getValStateForRegion(ASTContext &AstC, const ProgramStateRef &State, const MemRegion *R, bool Debug = false);
        bool gcEnabledHere(CheckerContext &C) const;
        bool propagateArgumentRootedness(CheckerContext &C, ProgramStateRef &State) const;
        SymbolRef getSymbolForResult(const Expr *Result, const ValueState *OldValS, ProgramStateRef &State, CheckerContext &C) const;
        
    public:
        void checkBeginFunction(CheckerContext &Ctx) const;
        void checkEndFunction(CheckerContext &Ctx) const;
        bool evalCall(const CallExpr *CE, CheckerContext &C) const;
        void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
        void checkPostStmt(const CStyleCastExpr *CE, CheckerContext &C) const;
        void checkPostStmt(const ArraySubscriptExpr *CE, CheckerContext &C) const;
        void checkPostStmt(const MemberExpr *ME, CheckerContext &C) const;
        void checkDerivingExpr(const Expr *Result, const Expr *Parent, bool ParentIsLoc, CheckerContext &C) const;
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
          PDP ExplainNoPropagationFromExpr(const clang::Expr *FromWhere,
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
REGISTER_MAP_WITH_PROGRAMSTATE(GCValueMap, SymbolRef, GCChecker::ValueState)
REGISTER_MAP_WITH_PROGRAMSTATE(GCRootMap, const MemRegion *, GCChecker::RootState)

template <typename callback>
SymbolRef GCChecker::walkToRoot(callback f, const ProgramStateRef &State, const MemRegion *Region)
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
            } else if (const SymbolDerived *SD = dyn_cast<SymbolDerived>(Sym)) {
                Region = SD->getRegion();
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
    if (!Region)
        return nullptr;
    while (true) {
        const VarRegion *VR = Region->getAs<VarRegion>();
        if (VR && VR->getDecl()->hasGlobalStorage()) {
            return VR;
        }
        const SymbolicRegion *SymR = Region->getAs<SymbolicRegion>();
        if (SymR) {
            const SymbolRegionValue *SymRV = dyn_cast<SymbolRegionValue>(SymR->getSymbol());
            if (!SymRV) {
                const SymbolDerived *SD = dyn_cast<SymbolDerived>(SymR->getSymbol());
                if (SD) {
                    Region = SD->getRegion();
                    continue;
                }
                break;
            }
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

PDP GCChecker::GCBugVisitor::VisitNode(
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

PDP GCChecker::GCValueBugVisitor::ExplainNoPropagationFromExpr(const clang::Expr *FromWhere,
    const ExplodedNode *N, PathDiagnosticLocation Pos, BugReporterContext &BRC, BugReport &BR)
{
    const MemRegion *Region = N->getState()->getSVal(FromWhere, N->getLocationContext()).getAsRegion();
    SValExplainer Ex(BRC.getASTContext());
    SymbolRef Parent = walkToRoot([&](SymbolRef Sym, const ValueState *OldVState) {
      return !OldVState;
    },
        N->getState(), Region);
    if (!Parent && Region) {
      Parent = walkToRoot([&](SymbolRef Sym, const ValueState *OldVState) {
        return !OldVState;
      },
          N->getState(), N->getState()->getSVal(Region).getAsRegion());
    }
    if (!Parent) {
        // May have been derived from a global. Check that
        const VarRegion *VR = Helpers::walk_back_to_global_VR(Region);
        if (VR) {
          BR.addNote("Derivation root was here", PathDiagnosticLocation::create(VR->getDecl(), BRC.getSourceManager()));
          const VarDecl *VD = VR->getDecl();
          if (VD) {
            if (!declHasAnnotation(VD,"julia_globally_rooted")) {
                return MakePDP(Pos, "Argument value was derived from unrooted global. May need GLOBALLY_ROOTED annotation.");                                  
            } else if (!isGCTrackedType(VD->getType())) {
                return MakePDP(Pos, "Argument value was derived global with untracked type. You may want to update the checker's type list");
            }
          }
          return MakePDP(Pos, "Argument value was derived from global, but the checker did not propagate the root. This may be a bug");                                            
        }
        return MakePDP(Pos, "Could not propagate root. Argument value was untracked.");
    }
    const ValueState *ValS = N->getState()->get<GCValueMap>(Parent);
    assert(ValS);
    if (ValS->isPotentiallyFreed()) {
        BR.addVisitor(llvm::make_unique<GCValueBugVisitor>(Parent));
        return MakePDP(Pos, "Root not propagated because it may have been freed. Tracking.");
    } else if (ValS->isRooted()) {
        BR.addVisitor(llvm::make_unique<GCValueBugVisitor>(Parent));
        return MakePDP(Pos, "Root was not propagated due to a bug. Tracking base value.");      
    } else {
        BR.addVisitor(llvm::make_unique<GCValueBugVisitor>(Parent));
        return MakePDP(Pos, "No Root to propagate. Tracking.");
    }
}

PDP GCChecker::GCValueBugVisitor::ExplainNoPropagation(
    const ExplodedNode *N, PathDiagnosticLocation Pos, BugReporterContext &BRC, BugReport &BR)
{
    if (N->getLocation().getAs<StmtPoint>()) {
        const clang::Stmt *TheS = N->getLocation().castAs<StmtPoint>().getStmt();
        const clang::CallExpr *CE = dyn_cast<CallExpr>(TheS);
        const clang::MemberExpr *ME = dyn_cast<MemberExpr>(TheS);
        if (ME)
            return ExplainNoPropagationFromExpr(ME->getBase(), N, Pos, BRC, BR);
        const clang::ArraySubscriptExpr *ASE = dyn_cast<ArraySubscriptExpr>(TheS);
        if (ASE)
            return ExplainNoPropagationFromExpr(ASE->getLHS(), N, Pos, BRC, BR);
        if (!CE)
            return nullptr;
        const clang::FunctionDecl *FD = CE->getDirectCallee();
        if (!FD)
            return nullptr;
        for (unsigned i = 0; i < FD->getNumParams(); ++i) {
            if (!declHasAnnotation(FD->getParamDecl(i), "julia_propagates_root"))
                continue;
            return ExplainNoPropagationFromExpr(CE->getArg(i), N, Pos, BRC, BR);
        }
        return nullptr;
    }
    return nullptr;
}

PDP GCChecker::GCValueBugVisitor::VisitNode(
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
    if (!OldValueState->isUntracked() &&
        NewValueState->isUntracked()) {
        PDP Diag = ExplainNoPropagation(N, Pos, BRC, BR);
        if (Diag)
            return Diag;
        return MakePDP(Pos, "Created untracked derivative.");
    } else if (NewValueState->isPotentiallyFreed() &&
        OldValueState->isJustAllocated()) {
      // std::make_shared< in later LLVM
      return MakePDP(Pos, "Value may have been GCed here.");
    } else if (NewValueState->isPotentiallyFreed() &&
      !OldValueState->isPotentiallyFreed()) {
      // std::make_shared< in later LLVM
      return MakePDP(Pos, "Value may have been GCed here (though I don't know why).");
    } else if (NewValueState->isRooted() &&
               OldValueState->isJustAllocated()) {
      return MakePDP(Pos, "Value was rooted here.");      
    } else if (!NewValueState->isRooted() &&
               OldValueState->isRooted()) {
      return MakePDP(Pos, "Root was released here.");    
    } else if (NewValueState->RootDepth !=
               OldValueState->RootDepth) {
      return MakePDP(Pos, "Rooting Depth changed here.");
    }
    return nullptr;
}

template <typename callback>
void GCChecker::report_error(callback f, CheckerContext &C, const char *message) const
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

void GCChecker::report_value_error(CheckerContext &C, SymbolRef Sym, const char *message, SourceRange range) const
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

bool GCChecker::gcEnabledHere(CheckerContext &C) const {
    int disabledAt = C.getState()->get<GCDisabledAt>();
    return disabledAt == (unsigned)-1;
}

bool GCChecker::propagateArgumentRootedness(CheckerContext &C, ProgramStateRef &State) const {
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
        auto Arg = State->getSVal(CE->getArg(idx++), LCtx->getParent());
        SymbolRef ArgSym = walkToRoot([](SymbolRef Sym, const ValueState *OldVState) {return !OldVState;},
            State, Arg.getAsRegion());
        if (!ArgSym) {
            continue;
        }
        const ValueState *ValS = State->get<GCValueMap>(ArgSym);
        if (!ValS) {
            report_error([&](BugReport *Report) {
                Report->addNote(
                  "Tried to find root for this parameter in inlined call",
                  PathDiagnosticLocation::create(P, C.getSourceManager()));
            }, C, "Missed allocation of parameter");
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
        State = State->set<GCValueMap>(ParamSym, *ValS);
        Change = true;
    }
    return Change;
}

void GCChecker::checkBeginFunction(CheckerContext &C) const {
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
    SValExplainer Ex(C.getASTContext());
    for (const auto P : FD->parameters()) {
        if (declHasAnnotation(P, "julia_require_rooted_slot")) {
            auto Param = State->getLValue(P, LCtx);
            const MemRegion *Root = State->getSVal(Param).getAsRegion();
            std::cout << "Rooted Slot " << Ex.Visit(Root) << std::endl;
            State = State->set<GCRootMap>(Root,
                RootState::getRoot(-1));
        } else if (isGCTrackedType(P->getType())) {
            auto Param = State->getLValue(P, LCtx);
            SymbolRef AssignedSym = State->getSVal(Param).getAsSymbol();
            assert(AssignedSym);
            State = State->set<GCValueMap>(AssignedSym,
                ValueState::getForArgument(FD, P));
            Change = true;
        }
    }
    if (Change) {
        C.addTransition(State);
    }
}

void GCChecker::checkEndFunction(CheckerContext &C) const {
    if (!C.inTopFrame())
        return;
    if (C.getState()->get<GCDepth>() > 0) {
        report_error(C, "Non-popped GC frame present at end of function");
    }
    if (C.getState()->get<GCDisabledAt>() == C.getStackFrame()->getIndex()) {
        C.addTransition(C.getState()->set<GCDisabledAt>((unsigned)-1));
    }
}

bool GCChecker::declHasAnnotation(const clang::Decl *D, const char *which) {
  for (const auto *Ann : D->specific_attrs<AnnotateAttr>()) {
      if (Ann->getAnnotation() == which)
          return true;
  }
  return false;
}

bool GCChecker::isFDAnnotatedNotSafepoint(const clang::FunctionDecl *FD) {
    return declHasAnnotation(FD, "julia_not_safepoint");
}

bool GCChecker::isBundleOfGCValues(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      if (Name.endswith_lower("typemap_intersection_env"))
          return true;
      return false;
    }, QT);
}

bool GCChecker::isGCTrackedType(QualType QT) {
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
          Name.endswith_lower("jl_typemap_level_t") ||
          Name.endswith_lower("jl_typename_t") ||
          Name.endswith_lower("jl_module_t") ||
          Name.endswith_lower("jl_tupletype_t") ||
          Name.endswith_lower("jl_gc_tracked_buffer_t") ||
          Name.endswith_lower("jl_tls_states_t") ||
          Name.endswith_lower("jl_binding_t") ||
          Name.endswith_lower("jl_ordereddict_t") ||
          Name.endswith_lower("jl_typemap_t") ||
          Name.endswith_lower("jl_unionall_t") ||
          Name.endswith_lower("jl_methtable_t") ||
          // Probably not technically true for these, but let's allow it
          Name.endswith_lower("typemap_intersection_env")
          ) {
          return true;
      }
      return false; 
    }, QT);
}

bool GCChecker::isGloballyRootedType(QualType QT) const {
    return isJuliaType([](StringRef Name) {
      return Name.endswith_lower("jl_sym_t");
    }, QT);
}

bool GCChecker::isSafepoint(const CallEvent &Call) const
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
      if (FD->getBuiltinID() != 0)
        isCalleeSafepoint = false;
      else
        isCalleeSafepoint = !isFDAnnotatedNotSafepoint(FD);
    }
  }
  return isCalleeSafepoint;
}

bool GCChecker::processPotentialSafepoint(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const
{
  if (!isSafepoint(Call))
    return false;
  bool DidChange = false;
  SValExplainer Ex(C.getASTContext());
  if (!gcEnabledHere(C))
    return false;
  const Decl *D = C.getLocationContext()->getDecl();
  const FunctionDecl *FD = D ? D->getAsFunction() : nullptr;
  SymbolRef SpeciallyRootedSymbol = nullptr;
  if (FD) {
    for (unsigned i = 0; i < FD->getNumParams(); ++i) {
        if (declHasAnnotation(FD->getParamDecl(i), "julia_temporarily_roots")) {
            SVal Test = Call.getArgSVal(i);
            // Walk backwards to find the symbol that we're tracking for this
            // value
            const MemRegion *Region = Test.getAsRegion();
            SpeciallyRootedSymbol = walkToRoot([&](SymbolRef Sym, const ValueState *OldVState) {
              return !OldVState;
            }, State, Region);
            break;
        }
    }
  }
  
  // Symbolically free all unrooted values.
  GCValueMapTy AMap = State->get<GCValueMap>();
  for (auto I = AMap.begin(), E = AMap.end(); I != E; ++I) {
      if (I.getData().isJustAllocated()) {
          if (SpeciallyRootedSymbol == I.getKey())
              continue;
          State = State->set<GCValueMap>(I.getKey(), ValueState::getFreed());
          DidChange = true;
      }
  }
  return DidChange;
}



const GCChecker::ValueState *GCChecker::getValStateForRegion(ASTContext &AstC, 
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

bool GCChecker::processArgumentRooting(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const {
    auto *Decl = Call.getDecl();
    const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
    if (!FD)
        return false;
    const MemRegion *RootingRegion = nullptr;
    SymbolRef RootedSymbol = nullptr;
    for (unsigned i = 0; i < FD->getNumParams(); ++i) {
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

bool GCChecker::processAllocationOfResult(const CallEvent &Call, CheckerContext &C, ProgramStateRef &State) const {
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
        for (unsigned i = 0; i < FD->getNumParams(); ++i) {
            if (declHasAnnotation(FD->getParamDecl(i), "julia_propagates_root")) {
                SVal Test = Call.getArgSVal(i);
                // Walk backwards to find the region that roots this value
                const MemRegion *Region = Test.getAsRegion();
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

void GCChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  bool didChange = processArgumentRooting(Call, C, State);
  didChange |= processPotentialSafepoint(Call, C, State);
  didChange |= processAllocationOfResult(Call, C, State);
  if (didChange)
    C.addTransition(State);
}

// Implicitly root values that were casted to globally rooted values
void GCChecker::checkPostStmt(const CStyleCastExpr *CE, CheckerContext &C) const {
    if (!isGloballyRootedType(CE->getTypeAsWritten()))
        return;
    SymbolRef Sym = C.getSVal(CE).getAsSymbol();
    if (!Sym)
        return;
    C.addTransition(C.getState()->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1)));
}

SymbolRef GCChecker::getSymbolForResult(const Expr *Result, const ValueState *OldValS, ProgramStateRef &State, CheckerContext &C) const
{
  auto ValLoc = C.getSVal(Result).getAs<Loc>();
  if (!ValLoc) {
      return nullptr;
  }
  SVal Loaded = State->getSVal(*ValLoc);
  SValExplainer Ex(C.getASTContext());
  if (Loaded.isUnknown()) {
    QualType QT = Result->getType();
    if (OldValS || GCChecker::isGCTrackedType(QT)) {
      Loaded = C.getSValBuilder().conjureSymbolVal(Result, C.getLocationContext(), QT,
                                            C.blockCount());
      State = State->bindLoc(*ValLoc, Loaded, C.getLocationContext());
    }
  }
  return Loaded.getAsSymbol();
}

void GCChecker::checkDerivingExpr(const Expr *Result, const Expr *Parent, bool ParentIsLoc, CheckerContext &C) const
{
    // This is the pointer
    SValExplainer Ex(C.getASTContext());
    auto ValLoc = C.getSVal(Result).getAs<Loc>();
    if (!ValLoc) {
        return;
    }
    ProgramStateRef State = C.getState();
    SVal ParentVal = C.getSVal(Parent);
    SymbolRef OldSym = ParentVal.getAsSymbol(true);
    const MemRegion *Region = C.getSVal(Parent).getAsRegion();
    const ValueState *OldValS = OldSym ? State->get<GCValueMap>(OldSym) : nullptr;
    SymbolRef NewSym = getSymbolForResult(Result, OldValS, State, C);
    if (!NewSym) {
        return;
    }
    if (Region) {
      const VarRegion *VR = Region->getAs<VarRegion>();
      bool inheritedState = false;
      ValueState NewValS = ValueState::getRooted(Region, -1);
      if (VR && isa<ParmVarDecl>(VR->getDecl())) {  
          // This works around us not being able to track symbols for struct/union
          // parameters very well.
          const auto *FD = dyn_cast<FunctionDecl>(C.getLocationContext()->getDecl());
          if (FD) {
            inheritedState = true; 
            NewValS = ValueState::getForArgument(FD, cast<ParmVarDecl>(VR->getDecl()));
          }
      } else {
        VR = Helpers::walk_back_to_global_VR(Region);
        if (VR && rootRegionIfGlobal(VR, State, C)) {
          inheritedState = true;
        }
      }
      if (inheritedState) {
        C.addTransition(State->set<GCValueMap>(NewSym, NewValS));
        return;
      }
    }
    if (!OldValS) {
        // This way we'll get better diagnostics
        if (isGCTrackedType(Result->getType())) {
            C.addTransition(State->set<GCValueMap>(NewSym, ValueState::getUntracked()));
        }
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
void GCChecker::checkPostStmt(const ArraySubscriptExpr *ASE, CheckerContext &C) const
{
    // Could be a root array, in which case this should be considered rooted
    // by that array.
    const MemRegion *Region = C.getSVal(ASE->getLHS()).getAsRegion();
    ProgramStateRef State = C.getState();
    SValExplainer Ex(C.getASTContext());
    if (Region && Region->getAs<ElementRegion>()) {
        if (const RootState *RS = State->get<GCRootMap>(
          Region->getAs<ElementRegion>()->getSuperRegion())) {
            ValueState ValS = ValueState::getRooted(Region, State->get<GCDepth>());
            SymbolRef NewSym = getSymbolForResult(ASE, &ValS, State, C);
            if (!NewSym)
                return;
            C.addTransition(C.getState()->set<GCValueMap>(NewSym, ValS));
            return;
        }
    }
    checkDerivingExpr(ASE, ASE->getLHS(), true, C);
}

void GCChecker::checkPostStmt(const MemberExpr *ME, CheckerContext &C) const
{
    checkDerivingExpr(ME, ME->getBase(), true, C);
}


void GCChecker::dumpState(const ProgramStateRef &State) {
    GCValueMapTy AMap = State->get<GCValueMap>();
    llvm::raw_ostream &Out = llvm::outs();
    Out << "State: " << "\n";
    for (auto I = AMap.begin(), E = AMap.end(); I != E; ++I) {
        I.getKey()->dumpToStream(Out);
    }
}

void GCChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {
    unsigned NumArgs = Call.getNumArgs();
    ProgramStateRef State = C.getState();
    bool isCalleeSafepoint = isSafepoint(Call);
    auto *Decl = Call.getDecl();
    const FunctionDecl *FD = Decl ? Decl->getAsFunction() : nullptr;
    SValExplainer Ex(C.getASTContext());
    if (!gcEnabledHere(C))
        return;
    for (unsigned idx = 0; idx < NumArgs; ++idx) {
        SVal Arg = Call.getArgSVal(idx);
        SymbolRef Sym = Arg.getAsSymbol();
        // Hack to work around passing unions/structs by value.
        if (auto LCV = Arg.getAs<nonloc::LazyCompoundVal>()) {
          const MemRegion *R = LCV->getRegion();
          if (R) {
            if (const SubRegion *SR = R->getAs<SubRegion>()) {
              if (const SymbolicRegion *SSR = SR->getSuperRegion()->getAs<SymbolicRegion>()) {
                Sym = SSR->getSymbol();
              }
            }
          }
        }
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

bool GCChecker::evalCall(const CallExpr *CE,
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
    } else if (name == "JL_GC_PROMISE_ROOTED") {
        SVal Arg = C.getSVal(CE->getArg(0));
        SymbolRef Sym = Arg.getAsSymbol();
        if (!Sym) {
            report_error(C, "Can not understand this promise.");
            return true;
        }
        C.addTransition(C.getState()->set<GCValueMap>(Sym, ValueState::getRooted(nullptr, -1)));
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

void GCChecker::checkBind(SVal LVal, SVal RVal, const clang::Stmt *S, CheckerContext &C) const {
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
        report_value_error(C, Sym, "Saw assignment to root, but missed the allocation");
        return;
    }
    if (RValState->isPotentiallyFreed())
        report_value_error(C, Sym, "Trying to root value which may have been GCed");
    if (!RValState->isRooted()) {
        C.addTransition(State->set<GCValueMap>(Sym, ValueState::getRooted(R, State->get<GCDepth>())));
    }
}

bool GCChecker::rootRegionIfGlobal(const MemRegion *R, ProgramStateRef &State, CheckerContext &C) const {
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

void GCChecker::checkLocation(SVal Loc, bool IsLoad, const Stmt *S, CheckerContext &C) const {
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

namespace clang {
namespace ento {
void registerGCChecker(CheckerManager &mgr) {
    mgr.registerChecker<GCChecker>();
}
}
}
