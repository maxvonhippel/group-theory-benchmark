import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic

/-!
# Problem K3

Suppose I is a closed interval of real numbers, and f and g are commuting continuous
maps of I into itself. Must they have a common fixed point?

## Formalization

We formalize this as a statement about continuous self-maps of the unit interval [0,1],
which is equivalent to any closed bounded interval by homeomorphism.
-/

/-- The main theorem: Do commuting continuous self-maps of [0,1] have a common fixed point? -/
theorem commuting_continuous_maps_have_common_fixed_point :
    ∀ (f g : C(unitInterval, unitInterval)),
      (∀ x, f (g x) = g (f x)) →
      ∃ x : unitInterval, f x = x ∧ g x = x := by
  sorry
