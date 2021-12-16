---
title: Formalisation of the Symmetry Book
---

[![build](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml)


```agda
{-# OPTIONS --without-K --exact-split #-}
```

## Chapter 2: Univalent mathematics


```agda
-- Formalization with --safe enabled
open import foundations.00-preamble public
open import foundations.02-pi public
open import foundations.03-natural-numbers public
open import foundations.04-inductive-types public
open import foundations.05-identity-types public
open import foundations.06-universes public
open import foundations.07-modular-arithmetic public
open import foundations.08-decidability-in-number-theory public
open import foundations.08-integers public
open import foundations.09-equivalences public
open import foundations.10-contractible-types public
open import foundations.11-fundamental-theorem public
open import foundations.12-truncation-levels public

-- Formalization with --safe disabled
open import foundations.13-function-extensionality public
open import foundations.14-propositional-truncation public
open import foundations.15-image public
open import foundations.16-finite-types public
open import foundations.17-univalence public
open import foundations.18-set-quotients public
open import foundations.23-pullbacks
open import foundations.24-pushouts
open import foundations.25-cubical-diagrams
open import foundations.26-descent
open import foundations.26-id-pushout
open import foundations.27-sequences
open import foundations.W-types
open import foundations.pointed-maps
open import foundations.spaces
open import categories
```

## Chapter 3 : The circle

```agda
open import the-circle.the-circle public
open import the-circle.integers public
open import the-circle.infinite-cyclic-types public
```

## Chapter 4 : Groups 

```agda
open import groups.abstract-groups public
open import groups.abstract-abelian-groups public
open import groups.abstract-group-actions public
open import groups.abstract-group-torsors public
open import groups.higher-groups public
open import groups.concrete-groups public
open import groups.examples-higher-groups public
open import groups.concrete-group-actions public
open import groups.sheargroups public
open import groups.furstenberg-groups public
```

## Chapter 5 : Subgroups

```agda
open import subgroups.abstract-subgroups public
```

### Everything

See the list of all Agda modules [here](everything.html).

