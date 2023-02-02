---
title: Quotient groups
---

```agda
module group-theory.quotient-groups where
```

## Idea

Given a normal subgroup `H` of `G`, the quotient group `q : G → G/H` such that `H ⊆ ker q`, and such that `q` satisfies the universal group with the property that any group homomorphism `f : G → K` such that `H ⊆ ker f` extends uniquely along `q` to a group homomorphism `G/H → K`.
