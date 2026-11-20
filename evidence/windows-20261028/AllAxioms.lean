import AnvBandit.Absorbing
import AnvBandit.AbsorbingAdapted
import AnvBandit.AbsorbingBound
import AnvBandit.AbsorbingCharge
import AnvBandit.AbsorbingCheck
import AnvBandit.AbsorbingConditional
import AnvBandit.AbsorbingConditionalCheck
import AnvBandit.AbsorbingCoupling
import AnvBandit.AbsorbingDrift
import AnvBandit.AbsorbingDriftCheck
import AnvBandit.AbsorbingError
import AnvBandit.AbsorbingErrorSeries
import AnvBandit.AbsorbingExpectation
import AnvBandit.AbsorbingFinal
import AnvBandit.AbsorbingFinalCheck
import AnvBandit.AbsorbingHolding
import AnvBandit.AbsorbingLoss
import AnvBandit.AbsorbingMeasurability
import AnvBandit.AbsorbingPublicCharge
import AnvBandit.AbsorbingSeries
import AnvBandit.AbsorbingTerminal
import AnvBandit.ActualAsymptotics
import AnvBandit.ActualCostCoefficients
import AnvBandit.ActualExplicit
import AnvBandit.ActualExplicitCanonical
import AnvBandit.ActualExplicitRegret
import AnvBandit.ActualGlobalPublic
import AnvBandit.ActualNodeArrival
import AnvBandit.ActualNodeCost
import AnvBandit.ActualNodeExpectation
import AnvBandit.ActualNodeFiniteCost
import AnvBandit.ActualNodeGrouping
import AnvBandit.ActualNodeMoments
import AnvBandit.ActualNodePublic
import AnvBandit.ActualPropagation
import AnvBandit.ActualPublicBudget
import AnvBandit.ActualSublinear
import AnvBandit.ActualWaiting
import AnvBandit.Adaptive
import AnvBandit.AlgCount
import AnvBandit.AlgLine
import AnvBandit.BaselineBounds
import AnvBandit.BaselineComparison
import AnvBandit.BaselineEncoding
import AnvBandit.BaselineExecution
import AnvBandit.BaselineKernel
import AnvBandit.BaselineLaw
import AnvBandit.BaselineObserved
import AnvBandit.BaselineProbability
import AnvBandit.BaselinePublicBudget
import AnvBandit.BaselineRealizedReward
import AnvBandit.BaselineRegret
import AnvBandit.BaselineSemantics
import AnvBandit.BaselineTrajectory
import AnvBandit.Batch
import AnvBandit.Bench
import AnvBandit.Benchmark
import AnvBandit.Check
import AnvBandit.CheckActualPublicBudget
import AnvBandit.CheckBaseline
import AnvBandit.CheckBaselineComparison
import AnvBandit.ConcreteKbeta
import AnvBandit.ConcreteKbetaCheck
import AnvBandit.Constants
import AnvBandit.Contact
import AnvBandit.Execution
import AnvBandit.ExecutionBounds
import AnvBandit.ExecutionContacts
import AnvBandit.ExecutionKernel
import AnvBandit.ExecutionLaw
import AnvBandit.ExecutionLawCheck
import AnvBandit.ExecutionObserved
import AnvBandit.ExecutionObservedCheck
import AnvBandit.ExecutionPhases
import AnvBandit.ExecutionProbability
import AnvBandit.ExecutionPropagation
import AnvBandit.ExecutionUCB
import AnvBandit.Explicit
import AnvBandit.ExplicitParameters
import AnvBandit.Exponential
import AnvBandit.ExponentialDP
import AnvBandit.FiniteCosts
import AnvBandit.GeneralTimeBounds
import AnvBandit.GlobalRegret
import AnvBandit.GlobalRegretCheck
import AnvBandit.GlobalTheorem
import AnvBandit.GlobalTheoremCheck
import AnvBandit.GoodEvent
import AnvBandit.Greedy
import AnvBandit.HeadTail
import AnvBandit.IdealV
import AnvBandit.MainTheorems
import AnvBandit.Model
import AnvBandit.Moments
import AnvBandit.NodeCost
import AnvBandit.Numerics
import AnvBandit.ObservedGlobal
import AnvBandit.ObservedGlobalCheck
import AnvBandit.ObservedRegret
import AnvBandit.ObservedRegretCheck
import AnvBandit.ObservedTrajectory
import AnvBandit.ObservedTrajectoryCheck
import AnvBandit.OriginalMain
import AnvBandit.OriginalMainCheck
import AnvBandit.P11Check
import AnvBandit.Potential
import AnvBandit.PotentialBridge
import AnvBandit.PotentialBridgeCheck
import AnvBandit.PotentialFn
import AnvBandit.Prefix
import AnvBandit.Prob
import AnvBandit.Propagation
import AnvBandit.PublicBudget
import AnvBandit.PublicDP
import AnvBandit.RealizedReward
import AnvBandit.RealizedRewardCheck
import AnvBandit.Regret
import AnvBandit.RemainingWait
import AnvBandit.RemainingWaitReal
import AnvBandit.RemainingWaitTail
import AnvBandit.Schedule
import AnvBandit.ScheduleLower
import AnvBandit.Serial
import AnvBandit.Statements
import AnvBandit.Terminal
import AnvBandit.TimeBounds
import AnvBandit.TrajectoryExpectation
import AnvBandit
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Compiler.Old
import Lean.Meta.RecExt

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.modules
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut moduleCount : Nat := 0
  let mut runtimeHelperCount : Nat := 0
  let mut used : Array Name := #[]
  for idx in [:modules.size] do
    let mod := modules[idx]!.module
    if mod.toString == "AnvBandit" || mod.toString.startsWith "AnvBandit." then
      moduleCount := moduleCount + 1
      let entries := env.header.moduleData[idx]!.constants.qsort (fun a b => Name.lt a.name b.name)
      logInfo m!"AUDIT_MODULE {mod} declarations={entries.size}"
      for info in entries do
        let name := info.name
        count := count + 1
        if info.isTheorem then theoremCount := theoremCount + 1
        if info.isAxiom then throwError "Project custom axiom: {name}"
        if info.isUnsafe then throwError "Project unsafe declaration: {name}"
        if info.isPartial then
          let some parent := Compiler.isUnsafeRecName? name
            | throwError "Non-generated project partial declaration: {name}"
          let some (.defnInfo parentInfo) := env.find? parent
            | throwError "Runtime companion lacks a kernel definition parent: {name}"
          if parentInfo.safety != .safe then throwError "Runtime companion parent is not safe: {name}"
          if parentInfo.levelParams != info.levelParams || parentInfo.type != info.type then
            throwError "Runtime companion type/levels differ from parent: {name}"
          let some helperModule := env.getModuleIdxFor? name
            | throwError "Runtime companion lacks module provenance: {name}"
          if env.getModuleIdxFor? parent != some helperModule then
            throwError "Runtime companion and parent have different modules: {name}"
          unless (← liftCoreM <| Meta.isRecursiveDefinition parent) do
            throwError "Runtime companion parent lacks recursive-definition tag: {name}"
          runtimeHelperCount := runtimeHelperCount + 1
          logInfo m!"AUDIT_COMPILER_RUNTIME_HELPER {name} parent={parent} safe_def=true recursive_tag=true type_levels_equal=true same_module=true"
        else
          let mut refs := info.type.getUsedConstants
          if let some value := info.value? (allowOpaque := true) then
            refs := refs ++ value.getUsedConstants
          for ref in refs do
            if let some refInfo := env.find? ref then
              if refInfo.isUnsafe || refInfo.isPartial then
                throwError "Safe kernel declaration {name} directly references unsafe/partial {ref}"
        let axioms ← collectAxioms name
        for ax in axioms do
          if !allowed.contains ax then throwError "Nonstandard axiom {ax} in {name}"
          if !used.contains ax then used := used.push ax
        logInfo m!"AUDIT_DECL {mod} :: {name} :: axioms={axioms.qsort Name.lt}"
  if count == 0 then throwError "No project declarations were checked"
  if moduleCount != 128 then throwError "Project module coverage mismatch: {moduleCount}"
  logInfo m!"ALL_PROJECT_AXIOMS_PASS modules={moduleCount} declarations={count} theorems={theoremCount} compiler_runtime_helpers={runtimeHelperCount} safe_kernel_references_checked=true allowed_used={used.qsort Name.lt}"
