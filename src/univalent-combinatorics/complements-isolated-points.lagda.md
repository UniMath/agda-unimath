# Complements of isolated points of finite types

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
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.equality-finite-types using
  ( has-decidable-equality-has-cardinality)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; UU-Fin; type-UU-Fin; equiv-UU-Fin-Level;
    equiv-UU-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

For any point `x` in a finite type `X` of cardinality `n+1`, we can construct its complement, which is a type of cardinality `n`.

## Definition

```agda
complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU-Fin-Level l1 k
complement-point-UU-Fin-Level {l1} {k} T =
  pair
    ( X')
    ( apply-universal-property-trunc-Prop H (mere-equiv-Prop (Fin k) X')
      ( λ e →
        unit-trunc-Prop
          ( equiv-equiv-Maybe
            { X = Fin k}
            { Y = X'}
            ( ( inv-equiv
                ( equiv-maybe-structure-isolated-point X isolated-x)) ∘e
              ( e)))))
  where
  X = pr1 (pr1 T)
  H = pr2 (pr1 T)
  x = pr2 T
  isolated-x : isolated-point X
  isolated-x = pair x (λ y → has-decidable-equality-has-cardinality H x y)
  X' : UU l1
  X' = complement-isolated-point X isolated-x

complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU-Fin k
complement-point-UU-Fin X = complement-point-UU-Fin-Level X

type-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU l1
type-complement-point-UU-Fin-Level X =
  type-UU-Fin-Level (complement-point-UU-Fin-Level X)

type-complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU lzero
type-complement-point-UU-Fin X =
  type-complement-point-UU-Fin-Level X

inclusion-complement-isolated-point :
  {l1 : Level} {X : UU l1} (x : isolated-point X) →
  complement-isolated-point X x → X
inclusion-complement-isolated-point x = pr1

natural-inclusion-equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : Id (map-equiv e (pr1 x)) (pr1 y)) →
  ( inclusion-complement-isolated-point y ∘
    map-equiv (equiv-complement-isolated-point e x y p)) ~
  ( map-equiv e ∘ inclusion-complement-isolated-point x)
natural-inclusion-equiv-complement-isolated-point e x y p (pair x' f) = refl

inclusion-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} (X : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  type-complement-point-UU-Fin-Level X → type-UU-Fin-Level (pr1 X)
inclusion-complement-point-UU-Fin-Level X = pr1

inclusion-complement-point-UU-Fin :
  {k : ℕ} (X : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  type-complement-point-UU-Fin X → type-UU-Fin (pr1 X)
inclusion-complement-point-UU-Fin X =
  inclusion-complement-point-UU-Fin-Level X

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
