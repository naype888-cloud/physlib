/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumThermodynamics.Landauer

/-!
# Landauer's bound at a temperature and for one bit

`LandauerProcess.landauerBound` states Landauer's principle with the inverse temperature `β`.
Here it is rewritten with the temperature `T`, where `β = 1 / (k_B T)`: the heat released into
the reservoir is at least `k_B T` times the entropy lost by the system, and erasing one bit,
`S(ρ) - S(ρ'_S) = log 2`, costs at least `k_B T log 2`.

## i. Key results

- `LandauerProcess.temperature_mul_systemEntropyDecrease_le_reservoirHeat` : the heat is at
  least `k_B T` times the entropy lost.
- `LandauerProcess.bit_le_reservoirHeat` : erasing one bit costs at least `k_B T log 2`.

## ii. References

* R. Landauer, *Irreversibility and heat generation in the computing process*,
  IBM J. Res. Dev. 5 (1961).
* Huanhai Zhou, `PhyslibAlpha.QuantumThermodynamics.Landauer` (#1409), on which this builds.
-/

@[expose] public section

noncomputable section

namespace QuantumThermodynamics

open Constants

namespace LandauerProcess

variable {S R : Type*} [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R] [Nonempty R]

/-- **Landauer's bound at temperature `T`.** The heat released into the reservoir is at least
`k_B T` times the entropy lost by the system. -/
lemma temperature_mul_systemEntropyDecrease_le_reservoirHeat (P : LandauerProcess S R)
    (hT : 0 < P.reservoirTemperature.val) :
    kB * (P.reservoirTemperature : ℝ) * P.systemEntropyDecrease ≤ P.reservoirHeat := by
  have hkT : 0 < kB * (P.reservoirTemperature : ℝ) := mul_pos kB_pos (by exact_mod_cast hT)
  have h := P.landauerBound
  rw [Temperature.β_toReal] at h
  calc kB * (P.reservoirTemperature : ℝ) * P.systemEntropyDecrease
      ≤ kB * (P.reservoirTemperature : ℝ) * (1 / (kB * (P.reservoirTemperature : ℝ)) *
          P.reservoirHeat) := mul_le_mul_of_nonneg_left h hkT.le
    _ = P.reservoirHeat := by rw [← mul_assoc, mul_one_div_cancel hkT.ne', one_mul]

/-- **Erasing one bit.** If the system loses `log 2` of entropy, the reservoir receives at least
`k_B T log 2` of heat. -/
lemma bit_le_reservoirHeat (P : LandauerProcess S R) (hT : 0 < P.reservoirTemperature.val)
    (hbit : P.systemEntropyDecrease = Real.log 2) :
    kB * (P.reservoirTemperature : ℝ) * Real.log 2 ≤ P.reservoirHeat :=
  hbit ▸ P.temperature_mul_systemEntropyDecrease_le_reservoirHeat hT

end LandauerProcess

end QuantumThermodynamics
