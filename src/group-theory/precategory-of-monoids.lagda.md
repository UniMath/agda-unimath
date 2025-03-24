# The precategory of monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.precategory-of-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext univalence truncations
open import category-theory.large-subprecategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids funext univalence truncations
open import group-theory.monoids funext univalence truncations
open import group-theory.precategory-of-semigroups funext univalence truncations
```

</details>

## Idea

The {{#concept "precategory of monoids" Agda=Monoid-Large-Precategory}} consists
of [monoids](group-theory.monoids.md) and
[homomorphisms of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The precategory of monoids as a subprecategory of the precategory of semigroups

```agda
Monoid-Large-Subprecategory :
  Large-Subprecategory (λ l → l) (λ l1 l2 → l2) Semigroup-Large-Precategory
Monoid-Large-Subprecategory =
  λ where
    .subtype-obj-Large-Subprecategory l →
      is-unital-prop-Semigroup {l}
    .subtype-hom-Large-Subprecategory G H is-unital-G is-unital-H →
      preserves-unit-hom-prop-Semigroup (G , is-unital-G) (H , is-unital-H)
    .contains-id-Large-Subprecategory G is-unital-G →
      preserves-unit-id-hom-Monoid (G , is-unital-G)
    .is-closed-under-composition-Large-Subprecategory
      G H K g f is-unital-G is-unital-H is-unital-K unit-g unit-f →
      preserves-unit-comp-hom-Monoid
        ( G , is-unital-G)
        ( H , is-unital-H)
        ( K , is-unital-K)
        ( g , unit-g)
        ( f , unit-f)
```

### The large precategory of monoids

```agda
Monoid-Large-Precategory : Large-Precategory lsuc (_⊔_)
Monoid-Large-Precategory =
  large-precategory-Large-Subprecategory Monoid-Large-Subprecategory
```

### The precategory of small monoids

```agda
Monoid-Precategory : (l : Level) → Precategory (lsuc l) l
Monoid-Precategory = precategory-Large-Precategory Monoid-Large-Precategory
```
