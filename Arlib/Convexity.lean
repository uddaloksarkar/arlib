/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Convexity.LogConcave
import Arlib.Convexity.Isoperimetry

/-
# Arlib.Convexity

Convex-geometric infrastructure for the analysis of sampling and volume algorithms:
log-concave functions, and the isoperimetric inequalities that lower-bound the
conductance of random walks over them.

Mathlib (`v4.15`) has no log-concavity, no isoperimetry, no Prékopa–Leindler and no
Brunn–Minkowski, so this area starts from the definitions.

## Modules

* `Arlib.Convexity.LogConcave` — log-concavity on `ℝ` in multiplicative form, and its
  closure under products.
* `Arlib.Convexity.Isoperimetry` — the product-to-minimum conversion for partition-based
  expansion bounds (fully proved, and reusable well beyond the log-concave setting), plus
  the one-dimensional isoperimetric inequality of Kannan–Lovász–Simonovits stated as an
  interface. The inequality itself is **not** proved here; see that file's docstring for
  precisely what is assumed and why.
-/
