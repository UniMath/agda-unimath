# The precategory of commutative semirings

```agda
module commutative-algebra.precategory-of-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import commutative-algebra.commutative-semirings

open import foundation.universe-levels

open import ring-theory.precategory-of-semirings
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
