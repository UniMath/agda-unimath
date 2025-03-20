# Premanifolds

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.premanifolds
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps funext
open import foundation.dependent-pair-types
open import foundation.mere-equivalences funext
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans funext
open import synthetic-homotopy-theory.mere-spheres funext
open import synthetic-homotopy-theory.pushouts funext
open import synthetic-homotopy-theory.spheres funext
open import synthetic-homotopy-theory.tangent-spheres funext
```

</details>

## Idea

An **`n`-dimensional premanifold** is a type `M` such that every element `x : M`
comes equipped with a
[tangent `n`-sphere](synthetic-homotopy-theory.tangent-spheres.md).

## Definitions

### Premanifolds

```agda
Premanifold : (l : Level) (n : ℕ) → UU (lsuc l)
Premanifold l n = Σ (UU l) (λ M → (x : M) → has-tangent-sphere n x)

module _
  {l : Level} (n : ℕ) (M : Premanifold l n)
  where

  type-Premanifold : UU l
  type-Premanifold = pr1 M

  tangent-sphere-Premanifold : (x : type-Premanifold) → mere-sphere lzero n
  tangent-sphere-Premanifold x =
    tangent-sphere-has-tangent-sphere n (pr2 M x)

  type-tangent-sphere-Premanifold : (x : type-Premanifold) → UU lzero
  type-tangent-sphere-Premanifold x =
    type-tangent-sphere-has-tangent-sphere n (pr2 M x)

  mere-equiv-tangent-sphere-Premanifold :
    (x : type-Premanifold) →
    mere-equiv (sphere n) (type-tangent-sphere-Premanifold x)
  mere-equiv-tangent-sphere-Premanifold x =
    mere-equiv-tangent-sphere-has-tangent-sphere n (pr2 M x)

  complement-Premanifold : (x : type-Premanifold) → UU l
  complement-Premanifold x =
    complement-has-tangent-sphere n (pr2 M x)

  inclusion-tangent-sphere-Premanifold :
    (x : type-Premanifold) →
    type-tangent-sphere-Premanifold x → complement-Premanifold x
  inclusion-tangent-sphere-Premanifold x =
    inclusion-tangent-sphere-has-tangent-sphere n (pr2 M x)

  inclusion-complement-Premanifold :
    (x : type-Premanifold) → complement-Premanifold x → type-Premanifold
  inclusion-complement-Premanifold x =
    inclusion-complement-has-tangent-sphere n (pr2 M x)

  coherence-square-Premanifold :
    (x : type-Premanifold) →
    coherence-square-maps
      ( inclusion-tangent-sphere-Premanifold x)
      ( terminal-map (type-tangent-sphere-Premanifold x))
      ( inclusion-complement-Premanifold x)
      ( point x)
  coherence-square-Premanifold x =
    coherence-square-has-tangent-sphere n (pr2 M x)

  cocone-Premanifold :
    (x : type-Premanifold) →
    cocone
      ( terminal-map (type-tangent-sphere-Premanifold x))
      ( inclusion-tangent-sphere-Premanifold x)
      ( type-Premanifold)
  cocone-Premanifold x =
    cocone-has-tangent-sphere n (pr2 M x)

  is-pushout-Premanifold :
    (x : type-Premanifold) →
    is-pushout
      ( terminal-map (type-tangent-sphere-Premanifold x))
      ( inclusion-tangent-sphere-Premanifold x)
      ( cocone-Premanifold x)
  is-pushout-Premanifold x =
    is-pushout-has-tangent-sphere n (pr2 M x)
```
