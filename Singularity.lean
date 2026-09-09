/-
# `Singularity` library root

Aggregator for the ODE / singularity-detection core.  Import an individual
`Singularity.*` module instead of this root when you only need one piece: this
file pulls in the whole library and is therefore the most expensive entry point.
-/

import Singularity.Poly
import Singularity.OdeSystem
import Singularity.Hamiltonian
import Singularity.Flow
import Singularity.Esa
import Singularity.ChangeOfVars
import Singularity.Singularity
import Singularity.Report
import Singularity.Tests
import Singularity.EnergyBounded
import Singularity.Integration
