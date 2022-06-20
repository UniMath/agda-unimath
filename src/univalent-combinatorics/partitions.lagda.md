---
title: Partitions of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.partitions where
```

## Idea

A partition of a finite type `X` can be defined in several equivalent ways:

- A partition is a subset `P` of the powerset of `X` such that each `U ⊆ X` in `P` is inhabited and each element `x : X` is in exactly one subset `U ⊆ X` in `P`.
- A partition is an equivalence relation on `X`
- A partition is a decomposition of `X` into a type of the form `Σ A B` where `A` is finite and `B` is a family of inhabited finite types, i.e., it consists of such `A` and `B` and an equivalence `X ≃ Σ A B`.

Note that the last description is subtly different from the notion of unlabeled partition (i.e., Ferrers diagram), because it only uses mere equivalences.
