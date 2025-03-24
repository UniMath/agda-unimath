# The precategory of commutative semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.precategory-of-commutative-semirings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import commutative-algebra.commutative-semirings funext univalence truncations

open import foundation.universe-levels

open import ring-theory.precategory-of-semirings funext univalence truncations
```

</details>

## Idea

The
{{#concept "precategory of commutative semirings" Agda=Commutative-Semiring-Large-Precategory}}
consists of
[commutative semirings](commutative-algebra.commutative-semirings.md) and
[homomorphisms of semirings](commutative-algebra.homomorphisms-commutative-semirings.md).

## Definitions

### The precategory of commutative semirings as a full subprecategory of semirings

```agda
Commutative-Semiring-Full-Large-Precategory :
  Full-Large-Subprecategory (λ l → l) Semiring-Large-Precategory
Commutative-Semiring-Full-Large-Precategory = is-commutative-prop-Semiring
```

### The large precategory of commutative semirings

```agda
Commutative-Semiring-Large-Precategory : Large-Precategory lsuc (_⊔_)
Commutative-Semiring-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Semiring-Large-Precategory)
    ( Commutative-Semiring-Full-Large-Precategory)
```

### The precategory of commutative semirings of universe level `l`

```agda
Commutative-Semiring-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Semiring-Precategory =
  precategory-Large-Precategory Commutative-Semiring-Large-Precategory
```
