# Wild representations of monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.wild-representations-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.endomorphisms funext univalence truncations
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.monoids funext univalence truncations

open import structured-types.morphisms-wild-monoids funext univalence truncations
```

</details>

## Idea

A coherent action of a [monoid](group-theory.monoids.md) `M` on a type `X`
requires an infinite hierarchy of explicit coherences. Instead, as a first order
approximation, we can consider **wild representations** of `M` on `X`,
consisting of a
[wild monoid homomorphism](structured-types.morphisms-wild-monoids.md) from `M`
to the [wild monoid](structured-types.wild-monoids.md) of
[endomorphisms](foundation.endomorphisms.md) on `X`.

## Definition

### Wild representations of a monoid in a type

```agda
wild-representation-type-Monoid :
  (l1 : Level) {l2 : Level} (M : Monoid l2) → UU (lsuc l1 ⊔ l2)
wild-representation-type-Monoid l1 M =
  Σ ( UU l1)
    ( λ X → hom-Wild-Monoid (wild-monoid-Monoid M) (endo-Wild-Monoid X))

module _
  {l1 l2 : Level} (M : Monoid l1)
  (ρ : wild-representation-type-Monoid l2 M)
  where

  type-wild-representation-type-Monoid : UU l2
  type-wild-representation-type-Monoid = pr1 ρ

  hom-action-wild-representation-type-Monoid :
    hom-Wild-Monoid
      ( wild-monoid-Monoid M)
      ( endo-Wild-Monoid type-wild-representation-type-Monoid)
  hom-action-wild-representation-type-Monoid = pr2 ρ

  action-wild-representation-type-Monoid :
    type-Monoid M → endo type-wild-representation-type-Monoid
  action-wild-representation-type-Monoid =
    map-hom-Wild-Monoid
      ( wild-monoid-Monoid M)
      ( endo-Wild-Monoid type-wild-representation-type-Monoid)
      ( hom-action-wild-representation-type-Monoid)

  preserves-mul-action-wild-representation-type-Monoid :
    { x y : type-Monoid M} →
    ( action-wild-representation-type-Monoid (mul-Monoid M x y)) ＝
    ( ( action-wild-representation-type-Monoid x) ∘
      ( action-wild-representation-type-Monoid y))
  preserves-mul-action-wild-representation-type-Monoid =
    preserves-mul-hom-Wild-Monoid
      ( wild-monoid-Monoid M)
      ( endo-Wild-Monoid type-wild-representation-type-Monoid)
      ( hom-action-wild-representation-type-Monoid)

  preserves-unit-action-wild-representation-type-Monoid :
    action-wild-representation-type-Monoid (unit-Monoid M) ＝ id
  preserves-unit-action-wild-representation-type-Monoid =
    preserves-unit-map-hom-Wild-Monoid
      ( wild-monoid-Monoid M)
      ( endo-Wild-Monoid type-wild-representation-type-Monoid)
      ( hom-action-wild-representation-type-Monoid)
```
