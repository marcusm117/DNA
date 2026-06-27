/- Aggregator for the shared figure-lemma library — BUILD-TARGET ROOT ONLY.
   `lake build Helpers` (via `scripts/safe_build.sh Helpers`) builds all helpers and only helpers.

   ⚠ Proof/step files must NOT import this aggregator — they import the SPECIFIC sub-module they use
   (`import Helpers.OffLine`, `import Helpers.SameSide`, …). Importing the aggregator would couple the
   file to every helper, so adding any new helper would force a rebuild of every importer. -/
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Area
import Helpers.RightAngle
import Helpers.Parallel
import Helpers.Angle
