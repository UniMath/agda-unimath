---
title: Complements of isolated points of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.complements-isolated-points where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (inv-equiv; _∘e_; _≃_; map-equiv)
open import foundation.equivalences-maybe using (equiv-equiv-Maybe)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl)
open import foundation.isolated-points using
  ( isolated-point; complement-isolated-point;
    equiv-maybe-structure-isolated-point; equiv-complement-isolated-point)
open import foundation.maybe using (Maybe)
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.equality-finite-types using
  ( has-decidable-equality-has-cardinality)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; UU-Fin; type-UU-Fin; equiv-UU-Fin-Level;
    equiv-UU-Fin; has-cardinality; has-cardinality-Prop;
    has-cardinality-type-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

For any point `x` in a finite type `X` of cardinality `n+1`, we can construct its complement, which is a type of cardinality `n`.

## Definition

### The complement of a point in a k-element type of arbitrary universe level

```agda
isolated-point-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l (succ-ℕ k)) →
  type-UU-Fin-Level X → isolated-point (type-UU-Fin-Level X)
pr1 (isolated-point-UU-Fin-Level X x) = x
pr2 (isolated-point-UU-Fin-Level X x) =
  has-decidable-equality-has-cardinality (has-cardinality-type-UU-Fin-Level X) x

type-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU l1
type-complement-point-UU-Fin-Level X =
  complement-isolated-point
    ( pr1 (pr1 X))
    ( isolated-point-UU-Fin-Level (pr1 X) (pr2 X))

equiv-maybe-structure-point-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l (succ-ℕ k)) →
  (x : type-UU-Fin-Level X) →
  Maybe (type-complement-point-UU-Fin-Level (pair X x)) ≃ type-UU-Fin-Level X
equiv-maybe-structure-point-UU-Fin-Level X x =
   equiv-maybe-structure-isolated-point
     ( type-UU-Fin-Level X)
     ( isolated-point-UU-Fin-Level X x)

has-cardinality-type-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} (X : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  has-cardinality k (type-complement-point-UU-Fin-Level X)
has-cardinality-type-complement-point-UU-Fin-Level (pair (pair X H) x) =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-Prop _
      ( type-complement-point-UU-Fin-Level (pair (pair X H) x)))
    ( λ e →
      unit-trunc-Prop
        ( equiv-equiv-Maybe
          ( ( inv-equiv
              ( equiv-maybe-structure-point-UU-Fin-Level (pair X H) x)) ∘e
            ( e))))
  
complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU-Fin-Level l1 k
pr1 (complement-point-UU-Fin-Level {l1} {k} T) =
  type-complement-point-UU-Fin-Level T
pr2 (complement-point-UU-Fin-Level {l1} {k} T) =
  has-cardinality-type-complement-point-UU-Fin-Level T

inclusion-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} (X : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  type-complement-point-UU-Fin-Level X → type-UU-Fin-Level (pr1 X)
inclusion-complement-point-UU-Fin-Level X = pr1
```

### The complement of a point in a k-element type of universe level zero

```agda
isolated-point-UU-Fin :
  {k : ℕ} (X : UU-Fin (succ-ℕ k)) → type-UU-Fin X →
  isolated-point (type-UU-Fin X)
isolated-point-UU-Fin = isolated-point-UU-Fin-Level

type-complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU lzero
type-complement-point-UU-Fin = type-complement-point-UU-Fin-Level

equiv-maybe-structure-point-UU-Fin :
  {k : ℕ} (X : UU-Fin (succ-ℕ k)) →
  (x : type-UU-Fin X) →
  Maybe (type-complement-point-UU-Fin (pair X x)) ≃ type-UU-Fin X
equiv-maybe-structure-point-UU-Fin = equiv-maybe-structure-point-UU-Fin-Level

has-cardinality-type-complement-point-UU-Fin :
  {k : ℕ} (X : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  has-cardinality k (type-complement-point-UU-Fin X)
has-cardinality-type-complement-point-UU-Fin =
  has-cardinality-type-complement-point-UU-Fin-Level
            
complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU-Fin k
complement-point-UU-Fin = complement-point-UU-Fin-Level

inclusion-complement-point-UU-Fin :
  {k : ℕ} (X : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  type-complement-point-UU-Fin X → type-UU-Fin (pr1 X)
inclusion-complement-point-UU-Fin X =
  inclusion-complement-point-UU-Fin-Level X
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ}
  (X Y : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  (e : equiv-UU-Fin-Level (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin-Level
    ( complement-point-UU-Fin-Level X)
    ( complement-point-UU-Fin-Level Y)
equiv-complement-point-UU-Fin-Level
  S T e p =
  equiv-complement-isolated-point e
    ( pair x (λ x' → has-decidable-equality-has-cardinality H x x'))
    ( pair y (λ y' → has-decidable-equality-has-cardinality K y y'))
    ( p)
  where
  H = pr2 (pr1 S)
  x = pr2 S
  K = pr2 (pr1 T)
  y = pr2 T

equiv-complement-point-UU-Fin :
  {k : ℕ} (X Y : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  (e : equiv-UU-Fin (pr1 X) (pr1 Y)) (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin (complement-point-UU-Fin X) (complement-point-UU-Fin Y)
equiv-complement-point-UU-Fin X Y e p =
  equiv-complement-point-UU-Fin-Level X Y e p
```

## Properties

### The map from a pointed (k+1)-element type to the complement of the point is an equivalence

```agda

```
