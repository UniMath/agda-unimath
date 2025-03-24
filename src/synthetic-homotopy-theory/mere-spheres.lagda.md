# Mere spheres

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.mere-spheres
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details></summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.mere-equivalences funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.dependent-products-propositions funext
open import foundation.universe-levels

open import synthetic-homotopy-theory.spheres funext univalence truncations
```

</details>

## Idea

A **mere `n`-sphere** is a type `X` that is
[merely equivalent](foundation.mere-equivalences.md) to the
[`n`-sphere](synthetic-homotopy-theory.spheres.md).

## Definitions

### The predicate of being a mere `n`-sphere

```agda
module _
  {l : Level} (n : ℕ) (X : UU l)
  where

  is-mere-sphere-Prop : Prop l
  is-mere-sphere-Prop = mere-equiv-Prop (sphere n) X

  is-mere-sphere : UU l
  is-mere-sphere = type-Prop is-mere-sphere-Prop

  is-prop-is-mere-sphere : is-prop is-mere-sphere
  is-prop-is-mere-sphere = is-prop-type-Prop is-mere-sphere-Prop
```

### Mere spheres

```agda
mere-sphere : (l : Level) (n : ℕ) → UU (lsuc l)
mere-sphere l n = Σ (UU l) (is-mere-sphere n)

module _
  {l : Level} (n : ℕ) (X : mere-sphere l n)
  where

  type-mere-sphere : UU l
  type-mere-sphere = pr1 X

  mere-equiv-mere-sphere : mere-equiv (sphere n) type-mere-sphere
  mere-equiv-mere-sphere = pr2 X
```
