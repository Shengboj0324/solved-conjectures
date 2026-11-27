import Conjectures.HeimNeuhauserPlanePartition
import Conjectures.HeimNeuhauserPlanePartitionBoundary
import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionCharacteristic
import Conjectures.HeimNeuhauserPlanePartitionChecks
import Conjectures.HeimNeuhauserPlanePartitionCosineInversion
import Conjectures.HeimNeuhauserPlanePartitionDampingBounds
import Conjectures.HeimNeuhauserPlanePartitionData
import Conjectures.HeimNeuhauserPlanePartitionFastSum
import Conjectures.HeimNeuhauserPlanePartitionFinite
import Conjectures.HeimNeuhauserPlanePartitionFourier
import Conjectures.HeimNeuhauserPlanePartitionFourierCentral
import Conjectures.HeimNeuhauserPlanePartitionFourierSign
import Conjectures.HeimNeuhauserPlanePartitionGeometricDamping
import Conjectures.HeimNeuhauserPlanePartitionIndices000To031
import Conjectures.HeimNeuhauserPlanePartitionIndices032To063
import Conjectures.HeimNeuhauserPlanePartitionIndices064To095
import Conjectures.HeimNeuhauserPlanePartitionIndices096To119
import Conjectures.HeimNeuhauserPlanePartitionIndices120To143
import Conjectures.HeimNeuhauserPlanePartitionIndices144To163
import Conjectures.HeimNeuhauserPlanePartitionIndices164To183
import Conjectures.HeimNeuhauserPlanePartitionIndices184To199
import Conjectures.HeimNeuhauserPlanePartitionIndices200To214
import Conjectures.HeimNeuhauserPlanePartitionIndices215To229
import Conjectures.HeimNeuhauserPlanePartitionIndices230To239
import Conjectures.HeimNeuhauserPlanePartitionIndices240To250
import Conjectures.HeimNeuhauserPlanePartitionInversion
import Conjectures.HeimNeuhauserPlanePartitionLargeRadius
import Conjectures.HeimNeuhauserPlanePartitionMiddleGrid
import Conjectures.HeimNeuhauserPlanePartitionMiddleIntegral
import Conjectures.HeimNeuhauserPlanePartitionMomentBounds
import Conjectures.HeimNeuhauserPlanePartitionMomentCells
import Conjectures.HeimNeuhauserPlanePartitionMomentCellsOne
import Conjectures.HeimNeuhauserPlanePartitionMomentCellsThree
import Conjectures.HeimNeuhauserPlanePartitionMomentCellsTwo
import Conjectures.HeimNeuhauserPlanePartitionMoments
import Conjectures.HeimNeuhauserPlanePartitionOuterIntegral
import Conjectures.HeimNeuhauserPlanePartitionPowerSeries
import Conjectures.HeimNeuhauserPlanePartitionRows
import Conjectures.HeimNeuhauserPlanePartitionSaddle
import Conjectures.HeimNeuhauserPlanePartitionScalar
import Conjectures.HeimNeuhauserPlanePartitionTailCellArithmetic
import Conjectures.HeimNeuhauserPlanePartitionTailCellsOne
import Conjectures.HeimNeuhauserPlanePartitionTailCellsThree
import Conjectures.HeimNeuhauserPlanePartitionTailCellsTwo
import Conjectures.HeimNeuhauserPlanePartitionTailCoverage
import Conjectures.HeimNeuhauserPlanePartitionTailExponential
import Conjectures.HeimNeuhauserPlanePartitionTailInterval
import Conjectures.HeimNeuhauserPlanePartitionTailParameters
import Conjectures.HeimNeuhauserPlanePartitionTailPointwise
import Conjectures.HeimNeuhauserPlanePartitionTheorems
import Conjectures.HeimNeuhauserPlanePartitionThirdMoment
import Conjectures.HeimNeuhauserPlanePartitionTilt
import Conjectures.HeimNeuhauserPlanePartitionTuranTail
import Conjectures.OrdinaryDarcais
import Conjectures.OrdinaryDarcaisCentral
import Conjectures.OrdinaryDarcaisPacked
import Conjectures.OrdinaryDarcaisRows
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command
import Lean.Data.Json

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let expectedModules : Array String := #["Conjectures.HeimNeuhauserPlanePartition", "Conjectures.HeimNeuhauserPlanePartitionBoundary", "Conjectures.HeimNeuhauserPlanePartitionCertificate", "Conjectures.HeimNeuhauserPlanePartitionCharacteristic", "Conjectures.HeimNeuhauserPlanePartitionChecks", "Conjectures.HeimNeuhauserPlanePartitionCosineInversion", "Conjectures.HeimNeuhauserPlanePartitionDampingBounds", "Conjectures.HeimNeuhauserPlanePartitionData", "Conjectures.HeimNeuhauserPlanePartitionFastSum", "Conjectures.HeimNeuhauserPlanePartitionFinite", "Conjectures.HeimNeuhauserPlanePartitionFourier", "Conjectures.HeimNeuhauserPlanePartitionFourierCentral", "Conjectures.HeimNeuhauserPlanePartitionFourierSign", "Conjectures.HeimNeuhauserPlanePartitionGeometricDamping", "Conjectures.HeimNeuhauserPlanePartitionIndices000To031", "Conjectures.HeimNeuhauserPlanePartitionIndices032To063", "Conjectures.HeimNeuhauserPlanePartitionIndices064To095", "Conjectures.HeimNeuhauserPlanePartitionIndices096To119", "Conjectures.HeimNeuhauserPlanePartitionIndices120To143", "Conjectures.HeimNeuhauserPlanePartitionIndices144To163", "Conjectures.HeimNeuhauserPlanePartitionIndices164To183", "Conjectures.HeimNeuhauserPlanePartitionIndices184To199", "Conjectures.HeimNeuhauserPlanePartitionIndices200To214", "Conjectures.HeimNeuhauserPlanePartitionIndices215To229", "Conjectures.HeimNeuhauserPlanePartitionIndices230To239", "Conjectures.HeimNeuhauserPlanePartitionIndices240To250", "Conjectures.HeimNeuhauserPlanePartitionInversion", "Conjectures.HeimNeuhauserPlanePartitionLargeRadius", "Conjectures.HeimNeuhauserPlanePartitionMiddleGrid", "Conjectures.HeimNeuhauserPlanePartitionMiddleIntegral", "Conjectures.HeimNeuhauserPlanePartitionMomentBounds", "Conjectures.HeimNeuhauserPlanePartitionMomentCells", "Conjectures.HeimNeuhauserPlanePartitionMomentCellsOne", "Conjectures.HeimNeuhauserPlanePartitionMomentCellsThree", "Conjectures.HeimNeuhauserPlanePartitionMomentCellsTwo", "Conjectures.HeimNeuhauserPlanePartitionMoments", "Conjectures.HeimNeuhauserPlanePartitionOuterIntegral", "Conjectures.HeimNeuhauserPlanePartitionPowerSeries", "Conjectures.HeimNeuhauserPlanePartitionRows", "Conjectures.HeimNeuhauserPlanePartitionSaddle", "Conjectures.HeimNeuhauserPlanePartitionScalar", "Conjectures.HeimNeuhauserPlanePartitionTailCellArithmetic", "Conjectures.HeimNeuhauserPlanePartitionTailCellsOne", "Conjectures.HeimNeuhauserPlanePartitionTailCellsThree", "Conjectures.HeimNeuhauserPlanePartitionTailCellsTwo", "Conjectures.HeimNeuhauserPlanePartitionTailCoverage", "Conjectures.HeimNeuhauserPlanePartitionTailExponential", "Conjectures.HeimNeuhauserPlanePartitionTailInterval", "Conjectures.HeimNeuhauserPlanePartitionTailParameters", "Conjectures.HeimNeuhauserPlanePartitionTailPointwise", "Conjectures.HeimNeuhauserPlanePartitionTheorems", "Conjectures.HeimNeuhauserPlanePartitionThirdMoment", "Conjectures.HeimNeuhauserPlanePartitionTilt", "Conjectures.HeimNeuhauserPlanePartitionTuranTail", "Conjectures.OrdinaryDarcais", "Conjectures.OrdinaryDarcaisCentral", "Conjectures.OrdinaryDarcaisPacked", "Conjectures.OrdinaryDarcaisRows"]
  let required : Array Name := #[`PlanePartition.divisorSquareSum_eq_sigma_two, `PlanePartition.planePartition_zero, `PlanePartition.planePartition_recurrence, `PlanePartition.planePartition_pos, `PlanePartition.rootDecrease_one_iff, `PlanePartition.rootDecrease_first_five, `PlanePartition.rootDecrease_six_to_eleven, `PlanePartition.original_root_of_turan, `PlanePartition.scalarCandidate_eval, `PlanePartition.strictTuran_of_certificates, `PlanePartition.strictTuran_finite, `PlanePartition.rootDecrease_through_250, `PlanePartition.original_root_finite, `PlanePartition.original_root_of_turan_tail, `PlanePartition.divisorSquareSum_upper, `PlanePartition.divisorSquareSum_lower, `PlanePartition.moment_summable, `PlanePartition.moment_continuousOn, `PlanePartition.moment_strictMono, `PlanePartition.geometric_le_mean, `PlanePartition.existsUnique_saddle, `PlanePartition.central_lower_integral, `PlanePartition.central_fourier_bound, `PlanePartition.normalized_fourier_pos_of_tail, `PlanePartition.damping_bound, `PlanePartition.phase_bound, `PlanePartition.mean_le_variance, `PlanePartition.positive_integral_at_saddle, `PlanePartition.strictTuran_of_tilted_center, `PlanePartition.strictTuran_of_saddle_estimates, `PlanePartition.weightedCoefficient_mul, `PlanePartition.weightedCoefficient_pow, `PlanePartition.exponentSeries_pow_coeff_nonneg, `PlanePartition.planePartition_tsum_coeff, `PlanePartition.weighted_exponent, `PlanePartition.planePartition_hasSum, `PlanePartition.centered_cosine_inversion, `PlanePartition.planePartition_fourier_inversion, `PlanePartition.strictTuran_of_two_saddle_bounds, `PlanePartition.variance_ge_geometric, `PlanePartition.thirdMoment_le_geometric, `PlanePartition.largeRadius_thirdMoment, `PlanePartition.moment_eq_shifted, `PlanePartition.shiftedMoment_enclosure, `PlanePartition.partialMoment_mono, `PlanePartition.momentNumerator_eq, `PlanePartition.thirdMoment_of_cell, `PlanePartition.thirdMoment_at_saddle, `PlanePartition.strictTuran_of_outer_integral, `PlanePartition.envelopeDamping_le, `PlanePartition.damping_ge_defect, `PlanePartition.damping_ge_outer, `PlanePartition.saddle_variance_lower, `PlanePartition.saddle_variance_upper, `PlanePartition.tailParameters_of_cell, `PlanePartition.tailParameters_at_saddle, `PlanePartition.intermediate_bin_certificate, `PlanePartition.outerRadii_bin_certificate, `PlanePartition.damping_ge_bin, `PlanePartition.outer_exponential_bound, `PlanePartition.gaussian_far_bound, `PlanePartition.middle_integral_bound, `PlanePartition.far_integral_bound, `PlanePartition.outer_integral_at_saddle, `PlanePartition.strictTuran_tail, `PlanePartition.heim_neuhauser_troeger_turan, `PlanePartition.heim_neuhauser_polynomization]
  let legacyPrefixes : Array String := #[]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  if env.header.isModule then
    throwError "All-owned audit must use legacy private-import mode"
  unless env.header.modules.size == env.header.moduleData.size do
    throwError "Imported module/data inventory size mismatch"
  let mut rawNames : NameSet := {}
  let mut seenModules : Array String := #[]
  for h : idx in [0:env.header.modules.size] do
    let mod := env.header.modules[idx]
    let moduleName := mod.module.toString
    let isProject := moduleName == "Solitaire" || moduleName.startsWith "Solitaire." ||
      moduleName == "Conjectures" || moduleName.startsWith "Conjectures."
    unless !isProject || expectedModules.contains moduleName do
      throwError "Unregistered project module in audit: {moduleName}"
    if expectedModules.contains moduleName then
      unless mod.hasData && mod.importAll do
        throwError "Project module lacks complete private data: {moduleName}"
      let data := env.header.moduleData[idx]!
      unless data.constNames == data.constants.map (·.name) do
        throwError "Serialized declaration names differ from their constants: {moduleName}"
      seenModules := seenModules.push moduleName
      let mut privateCount := 0
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "Serialized project declaration is invisible: {moduleName}: {name}"
        rawNames := rawNames.insert name
        if (privateToUserName? name).isSome then
          privateCount := privateCount + 1
      let record := Json.mkObj [
        ("tag", toJson "module"), ("module", toJson moduleName),
        ("modern", toJson data.isModule), ("import_all", toJson mod.importAll),
        ("has_data", toJson mod.hasData),
        ("names", toJson (data.constNames.map (·.toString))),
        ("private_count", toJson privateCount)]
      logInfo m!"ALL-OWNED-JSON {record.compress}"
  unless seenModules.size == expectedModules.size &&
      expectedModules.all seenModules.contains do
    throwError "Incomplete exact project module inventory"
  let mut audited : NameSet := {}
  let mut declarations := 0
  let mut theorems := 0
  let mut privateDeclarations := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) with
      | some mod => mod.module.toString
      | none => ""
    let userName := privateToUserName name
    let byModule := expectedModules.contains owner
    let bySerialized := rawNames.contains name
    let byLegacy := legacyPrefixes.any (fun p => userName.toString.startsWith p)
    if byModule || bySerialized || byLegacy then
      declarations := declarations + 1
      audited := audited.insert name
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .inductInfo _ => "inductive"
      if info.isTheorem then
        theorems := theorems + 1
      let privateName := privateToUserName? name
      if privateName.isSome then
        privateDeclarations := privateDeclarations + 1
      if let .axiomInfo _ := info then
        unless allowed.contains name do
          throwError "Unapproved project axiom {name}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
      let record := Json.mkObj [
        ("tag", toJson "declaration"), ("name", toJson name.toString),
        ("owner", toJson owner), ("kind", toJson kind),
        ("private_user_name", toJson (privateName.map (·.toString))),
        ("by_module", toJson byModule), ("by_serialized", toJson bySerialized),
        ("by_legacy_prefix", toJson byLegacy),
        ("axioms", toJson (axioms.map (·.toString)))]
      logInfo m!"ALL-OWNED-JSON {record.compress}"
  for name in rawNames.toArray do
    unless audited.contains name do
      throwError "Serialized project declaration escaped the audit: {name}"
  for name in required do
    let _ ← getConstInfo name
    unless audited.contains name do
      throwError "Required declaration is outside audited ownership: {name}"
    let record := Json.mkObj [("tag", toJson "required"), ("name", toJson name.toString)]
    logInfo m!"ALL-OWNED-JSON {record.compress}"
  let record := Json.mkObj [
    ("tag", toJson "passed"), ("modules", toJson seenModules.size),
    ("declarations", toJson declarations), ("theorems", toJson theorems),
    ("private_declarations", toJson privateDeclarations),
    ("raw_declarations", toJson rawNames.toArray.size),
    ("required", toJson required.size), ("allowed_axioms", toJson (allowed.map (·.toString)))]
  logInfo m!"ALL-OWNED-JSON {record.compress}"
