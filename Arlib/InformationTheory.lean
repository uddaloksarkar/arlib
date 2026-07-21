/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Basic
import Arlib.InformationTheory.Fano
import Arlib.InformationTheory.DataProcessing
import Arlib.InformationTheory.Submodular
import Arlib.InformationTheory.Variational
import Arlib.InformationTheory.Uniform
import Arlib.InformationTheory.ChainRule
import Arlib.InformationTheory.Defs
import Arlib.InformationTheory.Entropy
import Arlib.InformationTheory.Gibbs
import Arlib.InformationTheory.Relabel

/-!
# `Arlib.InformationTheory`

Area root: discrete Shannon information theory over a finite probability space —
entropy, conditional entropy, mutual information, KL divergence, and the
inequalities that lower-bound arguments run on (Gibbs, data processing, Fano).

Mathlib provides none of this for discrete random variables, so the area is
self-contained on top of `Arlib.Probability.FinProb`.
-/
