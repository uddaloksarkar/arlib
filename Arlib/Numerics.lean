/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
/-
# Arlib.Numerics

Numerical-analysis infrastructure: reasoning about the error incurred when a
real-valued expression is evaluated in finite precision rather than exactly.

The area's content is a **multiplicative** error-propagation framework — an
expression DAG whose nodes each carry a *relative* error bound, propagated
bottom-up by one rule per operation, together with the master theorem saying
that the propagated bound really does dominate the true relative error of the
whole computation. This extends the classical Bauer (1974) computational-DAG
analysis, which tracks *additive* errors; multiplicative errors are what
sampling-accuracy arguments need, since there the quantity of interest is a
ratio of probabilities.

The framework is abstract over the rounding scheme: a rounding map is any
function satisfying the relative-error contract `|rnd x - x| ≤ ε·|x|`, so the
results apply to IEEE-754 arithmetic, to correctly-rounded special functions,
and to any other scheme meeting that contract.

This is the area root; it re-exports the modules below.
-/

import Arlib.Numerics.ErrorPropagation
