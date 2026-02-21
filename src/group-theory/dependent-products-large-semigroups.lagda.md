# Dependent products of large semigroups

```agda
module group-theory.dependent-products-large-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-products-cumulative-large-sets
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.large-semigroups
```

</details>

## Idea

The dependent product of a family of
[large semigroups](group-theory.large-semigroups.md) is a large semigroup.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (G : (a : A) → Large-Semigroup α β)
  where

  cumulative-large-set-Π-Large-Semigroup :
    Cumulative-Large-Set (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  cumulative-large-set-Π-Large-Semigroup =
    Π-Cumulative-Large-Set A (λ a → cumulative-large-set-Large-Semigroup (G a))

  type-Π-Large-Semigroup : (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Semigroup l = (a : A) → type-Large-Semigroup (G a) l

  mul-Π-Large-Semigroup :
    {l1 l2 : Level} →
    type-Π-Large-Semigroup l1 → type-Π-Large-Semigroup l2 →
    type-Π-Large-Semigroup (l1 ⊔ l2)
  mul-Π-Large-Semigroup f g a = mul-Large-Semigroup (G a) (f a) (g a)

  preserves-sim-mul-Π-Large-Semigroup :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Π-Large-Semigroup)
      ( mul-Π-Large-Semigroup)
  preserves-sim-mul-Π-Large-Semigroup g g' h h' g~g' h~h' a =
    preserves-sim-mul-Large-Semigroup
      ( G a)
      ( g a)
      ( g' a)
      ( h a)
      ( h' a)
      ( g~g' a)
      ( h~h' a)

  sim-preserving-binary-operator-mul-Π-Large-Semigroup :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Π-Large-Semigroup)
  sim-preserving-binary-operator-mul-Π-Large-Semigroup =
    make-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Π-Large-Semigroup)
      ( mul-Π-Large-Semigroup)
      ( preserves-sim-mul-Π-Large-Semigroup)

  abstract
    associative-mul-Π-Large-Semigroup :
      {l1 l2 l3 : Level}
      (f : type-Π-Large-Semigroup l1)
      (g : type-Π-Large-Semigroup l2)
      (h : type-Π-Large-Semigroup l3) →
      mul-Π-Large-Semigroup (mul-Π-Large-Semigroup f g) h ＝
      mul-Π-Large-Semigroup f (mul-Π-Large-Semigroup g h)
    associative-mul-Π-Large-Semigroup f g h =
      eq-htpy (λ a → associative-mul-Large-Semigroup (G a) (f a) (g a) (h a))

  Π-Large-Semigroup : Large-Semigroup (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Semigroup =
    λ where
      .cumulative-large-set-Large-Semigroup →
        cumulative-large-set-Π-Large-Semigroup
      .sim-preserving-binary-operator-mul-Large-Semigroup →
        sim-preserving-binary-operator-mul-Π-Large-Semigroup
      .associative-mul-Large-Semigroup →
        associative-mul-Π-Large-Semigroup
```
