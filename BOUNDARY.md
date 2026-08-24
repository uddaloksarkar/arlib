# Arlib / ArlibCommunity hard boundary

Arlib is the reusable mathematical foundation.  ArlibCommunity is the only
owner of named algorithms, reductions, concrete chain analyses, and explicit
resource bounds.  The dependency direction is permanently

```text
Mathlib -> Arlib -> ArlibCommunity
```

In particular, no Arlib module may import `ArlibCommunity`.  A theorem belongs
in Arlib when its statement is independent of a particular procedure and cost
model.  A theorem belongs in ArlibCommunity when it establishes correctness,
approximation, mixing, sample, query, transition, communication, or size bounds
for a procedure or concrete construction.

Mixed files must be split.  Reusable representations and mathematical lemmas
remain in Arlib; downstream procedures and analyses move to ArlibCommunity.
`BOUNDARY_MANIFEST.tsv` records the initial disposition of every source module.
`scripts/BoundaryAudit.sh` enforces the import half of the boundary in CI.

