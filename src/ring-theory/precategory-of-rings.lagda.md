# The precategory of rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.precategory-of-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.universe-levels

open import ring-theory.homomorphisms-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The **(large) precategory of rings** consists of [rings](ring-theory.rings.md)
and [ring homomorphisms](ring-theory.homomorphisms-rings.md).

## Definitions

### The large precategory of rings

```agda
Ring-Large-Precategory : Large-Precategory (lsuc) (_⊔_)
Ring-Large-Precategory =
  make-Large-Precategory
    ( Ring)
    ( hom-set-Ring)
    ( λ {l1} {l2} {l3} {R} {S} {T} → comp-hom-Ring R S T)
    ( λ {l} {R} → id-hom-Ring R)
    ( λ {l1} {l2} {l3} {l4} {R} {S} {T} {U} → associative-comp-hom-Ring R S T U)
    ( λ {l1} {l2} {R} {S} → left-unit-law-comp-hom-Ring R S)
    ( λ {l1} {l2} {R} {S} → right-unit-law-comp-hom-Ring R S)
```

### The precategory of rings at a universe level

```agda
Ring-Precategory : (l : Level) → Precategory (lsuc l) l
Ring-Precategory = precategory-Large-Precategory Ring-Large-Precategory
```
