# `0`-acyclic maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.0-acyclic-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.epimorphisms-with-respect-to-sets funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.surjective-maps funext univalence truncations
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.truncated-acyclic-maps funext univalence truncations
```

</details>

## Idea

A **`0`-acyclic map** is a map whose [fibers](foundation-core.fibers-of-maps.md)
are [`0`-acyclic types](synthetic-homotopy-theory.0-acyclic-types.md), meaning
that their [suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic maps as the
[surjective maps](foundation.surjective-maps.md).

## Definition

### The predicate of being a `0`-acyclic map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-0-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-0-acyclic-map-Prop = is-truncated-acyclic-map-Prop (zero-𝕋)

  is-0-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-0-acyclic-map f = type-Prop (is-0-acyclic-map-Prop f)

  is-prop-is-0-acyclic-map :
    (f : A → B) → is-prop (is-0-acyclic-map f)
  is-prop-is-0-acyclic-map f =
    is-prop-type-Prop (is-0-acyclic-map-Prop f)
```

## Properties

### A map is `0`-acyclic if and only if it is surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-surjective-is-0-acyclic-map :
    is-0-acyclic-map f → is-surjective f
  is-surjective-is-0-acyclic-map ac =
    is-surjective-is-epimorphism-Set
      ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type f ac)

  is-0-acyclic-map-is-surjective :
    is-surjective f → is-0-acyclic-map f
  is-0-acyclic-map-is-surjective s =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type f
      ( is-epimorphism-is-surjective-Set s)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
