# Unchecked continuation drafts

These five modules have not passed Lean compilation. They are excluded from the project import tree, theorem inventory, and successful-check claims. Do not treat them as proved theorems.

The attempted canonical dependency build did not reach these modules: more than 1,500 required project/vendor compiled artifacts were absent from the restored partial cache. A supplementary combined-source experiment was abandoned because upstream private declarations rely on separate module environments. No result from that experiment is certified.

The drafts address positivity and section counts of polarization roots, isogeny-degree cancellation, actual root construction, finite-field rank preservation, and moduli representatives. Their intended mathematical boundary still includes uniform very ampleness and the unconditional elliptic-map theorem.

Resume by restoring the five files under `SupersingularCurves/Geometry`, restoring their aggregate imports, and running the canonical Lake build after completing the dependency cache. Fix any elaboration errors, then run a transitive axiom audit before adding them to the proved inventory. The moved pairing lemma is now in `ScalarFrobeniusTateQuotientPairing.lean`.
