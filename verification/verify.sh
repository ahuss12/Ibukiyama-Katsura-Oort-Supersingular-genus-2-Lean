#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/project-build.log 2>&1
python3 verification/check_sources.py > verification/source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/source-audit.log 2>&1
lake env lean verification/BasisExamples.lean > verification/basis-examples.log 2>&1
lake env lean verification/TorsionExamples.lean > verification/torsion-examples.log 2>&1
lake env lean verification/GeometricExamples.lean > verification/geometric-examples.log 2>&1
lake env lean verification/SimpleRootExamples.lean > verification/simple-root-examples.log 2>&1
lake env lean verification/SuperspecialExamples.lean > verification/superspecial-examples.log 2>&1
lake env lean verification/GeneralGenusTwoExamples.lean > verification/general-genus-two-examples.log 2>&1
lake env lean verification/CohomologyExamples.lean > verification/cohomology-examples.log 2>&1
lake env lean verification/RepartitionExamples.lean > verification/repartition-examples.log 2>&1
lake env lean verification/ResidueExamples.lean > verification/residue-examples.log 2>&1
lake env lean verification/FrobeniusCechExamples.lean > verification/frobenius-cech-examples.log 2>&1
lake env lean verification/CartierVerschiebungExamples.lean > verification/cartier-verschiebung-examples.log 2>&1
lake env lean verification/GenusTwoPRankExamples.lean > verification/genus-two-prank-examples.log 2>&1
lake env lean verification/Checkpoint21Audit.lean > verification/checkpoint-21-axiom-audit.log 2>&1
lake env lean verification/SupersingularGeometryExamples.lean > verification/supersingular-geometry-examples.log 2>&1
lake env lean verification/Checkpoint22Audit.lean > verification/checkpoint-22-axiom-audit.log 2>&1
lake env lean Audit.lean > verification/axiom-audit.log 2>&1
printf 'Build, source audit, basis examples, torsion examples, geometric examples, simple-root examples, superspecial examples, general genus-two examples, cohomology examples, repartition examples, residue examples, Frobenius/Cech examples, and transitive axiom audit passed.\n'
lake env lean verification/Checkpoint23Examples.lean
lake env lean verification/Checkpoint23Audit.lean

lake env lean verification/Checkpoint24Examples.lean
lake env lean verification/Checkpoint24Audit.lean

lake env lean verification/Checkpoint25Examples.lean
lake env lean verification/Checkpoint25Audit.lean

lake env lean verification/Checkpoint26Examples.lean
lake env lean verification/Checkpoint26Audit.lean
