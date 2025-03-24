# The precategory of semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.precategory-of-semirings
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

open import ring-theory.homomorphisms-semirings funext univalence truncations
open import ring-theory.semirings funext univalence truncations
```

</details>

## Idea

The {{#concet "precategory of semirings" Agda=Semiring-Large-Precategory}}
consists of [semirings](ring-theory.semirings.md) and
[homomorphisms of semirings](ring-theory.homomorphisms-semirings.md).

## Definitions

### The large precategory of semirings

```agda
Semiring-Large-Precategory : Large-Precategory lsuc (_⊔_)
Semiring-Large-Precategory =
  make-Large-Precategory
    ( Semiring)
    ( hom-set-Semiring)
    ( λ {l1} {l2} {l3} {R} {S} {T} → comp-hom-Semiring R S T)
    ( λ {l} {R} → id-hom-Semiring R)
    ( λ {l1} {l2} {l3} {l4} {R} {S} {T} {U} →
      associative-comp-hom-Semiring R S T U)
    ( λ {l1} {l2} {R} {S} → left-unit-law-comp-hom-Semiring R S)
    ( λ {l1} {l2} {R} {S} → right-unit-law-comp-hom-Semiring R S)
```

### The precategory of small semirings

```agda
Semiring-Precategory : (l : Level) → Precategory (lsuc l) l
Semiring-Precategory = precategory-Large-Precategory Semiring-Large-Precategory
```
