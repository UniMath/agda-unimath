---
title: Formalisation of the Symmetry Book
---

[![build](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml)


```agda
{-# OPTIONS --without-K --exact-split #-}
```

## Foundations

```agda
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
```

## Univalent Foundations

```agda
open import univalent-foundations.13-function-extensionality public
open import univalent-foundations.13-function-extensionality-solutions public
open import univalent-foundations.14-propositional-truncation public
open import univalent-foundations.15-image public
open import univalent-foundations.16-finite-types public
open import univalent-foundations.17-univalence public
open import univalent-foundations.18-set-quotients public
open import univalent-foundations.W-types public
open import univalent-foundations.pointed-types public

```

## Categories

```agda
open import categories.categories public
open import categories.functors public
open import categories.natural-transformations public
open import categories.large-categories public
```

## The circle

```agda
open import the-circle.the-circle public
open import the-circle.universal-cover public
open import the-circle.integers public
open import the-circle.cyclic-types public
open import the-circle.infinite-cyclic-types public
```

## Synthetic Homotopy Theory

```agda
open import synthetic-homotopy-theory.23-pullbacks public
open import synthetic-homotopy-theory.24-pushouts public
open import synthetic-homotopy-theory.25-cubical-diagrams public
open import synthetic-homotopy-theory.26-descent public
open import synthetic-homotopy-theory.26-id-pushout public
open import synthetic-homotopy-theory.27-sequences public
open import synthetic-homotopy-theory.spaces public
```

## Groups 

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

## Subgroups

```agda
open import subgroups.abstract-subgroups public
```

### Everything

See the list of all Agda modules [here](everything.html).

