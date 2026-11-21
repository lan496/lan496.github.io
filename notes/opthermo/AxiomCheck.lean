import OpThermo

/-! 主定理が `sorry` や追加の公理に依存しないことを確かめる。
`lake env lean AxiomCheck.lean` で実行する。出力が
`[propext, Classical.choice, Quot.sound]` (Lean 標準の公理) だけなら問題ない。 -/

open OpThermo OpThermo.Adiabatic OpThermo.Adiabatic.Calibration OpThermo.ExtensiveStructure

#print axioms length_exists
#print axioms length_unique
#print axioms compatible_of_represents
#print axioms gravity_work_eq
#print axioms WeightStatics.compatible_of_mechanicalLaw
#print axioms WeightStatics.compatible_with_balance
#print axioms AdiabaticOps.pathIndependent_iff_of_mechanicalLaw
#print axioms Laboratory.stationary_congr
#print axioms stationary_not_state_property
#print axioms Laboratory.Clock.time_exists
#print axioms Laboratory.Clock.compatible
#print axioms Laboratory.Clock.stationary_wait
#print axioms AdiabaticProcesses.internalEnergy_spec
#print axioms AdiabaticProcesses.internalEnergy_unique
#print axioms AdiabaticOps.pathIndependent_iff_of_compatible
#print axioms AdiabaticOps.internalEnergy_of_compatible
#print axioms pathIndependent_depends_on_mass
#print axioms cancel
#print axioms entropy_principle
#print axioms entropy_add
#print axioms entropy_smul
#print axioms entropy_unique
#print axioms exchange_equilibrium
#print axioms exchange_direction
#print axioms gibbs_criterion
#print axioms CompositeOps.toAdiabatic
#print axioms CompositeOps.energy_spec
#print axioms CompositeOps.energy_extensive
#print axioms entropy_extensive
#print axioms fundamental_relation_multi
#print axioms euler_homogeneous
#print axioms gibbs_euler
#print axioms CompositeOps.isolated_process_lowers_gibbs
#print axioms CompositeOps.reachable_of_gibbs_le
#print axioms gibbs_large_reservoir
#print axioms large_reservoir_criterion
#print axioms gibbs_hasDerivAt
#print axioms model_entropy
#print axioms entropy_bisect
#print axioms entropy_monotone_of_stirring
#print axioms temperature_pos
#print axioms exchange_temperature
#print axioms zeroth_law
#print axioms heat_flows_to_colder
#print axioms ideal_gas
#print axioms ideal_gas_law
#print axioms entropy_calorimetry
#print axioms contact_isLocalMax
#print axioms Adiabatic.Calibration.caratheodory
#print axioms idealGas_temperature
#print axioms idealGas_law
#print axioms idealGas_homogeneous
#print axioms idealGas_hasDerivAt_V
#print axioms unattainability
#print axioms idealGas_unique
#print axioms fundamental_relation_forms
#print axioms Adiabatic.helmholtz_criterion
#print axioms CompositeOps.max_work
#print axioms CompositeOps.enthalpy_change
#print axioms helmholtz_hasDerivAt
#print axioms enthalpy_hasDerivAt
#print axioms total_entropy_helmholtz
#print axioms Adiabatic.energy_minimum
#print axioms Adiabatic.enthalpy_minimum
#print axioms large_reservoir_entropy
#print axioms temperature_rescale
#print axioms kelvin_ratio
#print axioms heatCapacity_eq
#print axioms heatCapacity_pos
#print axioms entropy_hasDerivAt_temperature
#print axioms Adiabatic.concaveOn_of_partition
#print axioms concave_continuousOn
#print axioms superadditive_of_concave
#print axioms Adiabatic.contact_reversible_of_equal_temp
#print axioms model_reach_all
