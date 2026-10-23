module

public import RP2.PaperResponse
public import RP2.TetrahedralTensor
public import RP2.AveragingInterface

public section

/-!
# Public mathematical interfaces for the RP² note

* `RP2.Paper.family_bound` states the analytic inequality using `R`, `T`, and `q`.
* `RP2.Paper.R_hermitian_eq` and `R_hermitian_symm` fix conjugation conventions.
* `RP2.tetraAction_average_Q_zero` is the twelve-rotation tensor cancellation.
* `RP2.AveragingSystem.partition_replace_all` is exact remainder normalization.
* `RP2.AveragingSystem.correlation_bound` is the reusable positive-remainder
  product estimate, with all locality, positivity, and symmetry assumptions
  stated explicitly in the abstract averaging system.
-/
