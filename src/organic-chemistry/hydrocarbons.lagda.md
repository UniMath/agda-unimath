---
title: Hydrocarbons
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.hydrocarbons where
```

## Idea

We define the type of all theoretically possible hydrocarbons, correctly accounting for the symmetries between hydrocarbons and the different isomers.

Hydrocarbons are built out of carbon and hydrogen atoms. The symmetry group of an isolated carbon atom in 3-space is the alternating group `A₄`, where the number 4 comes from the number of bonds a carbon atom makes in a molecule.

Bonds in hydrocarbons can appear as single bonds, double bonds, and triple bonds, but there are no quadruple bonds. 
