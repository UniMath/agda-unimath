# Algebras over monads on precategories

```agda
module category-theory.algebras-monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-precategories
open import category-theory.monads-on-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Idea

An
{{#concept "algebra" Disambiguation="over a monad on a precategory" Agda=algebra-monad-Precategory}}
over a [monad](category-theory.monads-on-precategories.md) `T` consists of an
object `A` and morphism `a : TA → A` satisfying two compatibility laws:

- **Unit law**: `a ∘ η_A = id_A`
- **Multiplication law**: `a ∘ Ta = a ∘ μ_A`

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  {A : obj-Precategory C}
  (a : hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
  where

  has-unit-law-algebra-monad-Precategory : UU l2
  has-unit-law-algebra-monad-Precategory =
    comp-hom-Precategory C a (hom-unit-monad-Precategory C T A) ＝
    id-hom-Precategory C

  has-mul-law-algebra-monad-Precategory : UU l2
  has-mul-law-algebra-monad-Precategory =
    comp-hom-Precategory C a (hom-endofunctor-monad-Precategory C T a) ＝
    comp-hom-Precategory C a (hom-mul-monad-Precategory C T A)

  is-algebra-monad-Precategory : UU l2
  is-algebra-monad-Precategory =
    has-unit-law-algebra-monad-Precategory ×
    has-mul-law-algebra-monad-Precategory

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  algebra-monad-Precategory : UU (l1 ⊔ l2)
  algebra-monad-Precategory =
    Σ ( obj-Precategory C)
      ( λ A →
        Σ ( hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
          ( λ a → is-algebra-monad-Precategory C T a))

  obj-algebra-monad-Precategory : algebra-monad-Precategory → obj-Precategory C
  obj-algebra-monad-Precategory = pr1

  hom-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    hom-Precategory C
      ( obj-endofunctor-monad-Precategory C T (obj-algebra-monad-Precategory f))
      ( obj-algebra-monad-Precategory f)
  hom-algebra-monad-Precategory f = pr1 (pr2 f)

  comm-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    is-algebra-monad-Precategory C T (hom-algebra-monad-Precategory f)
  comm-algebra-monad-Precategory f = pr2 (pr2 f)

  unit-law-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    has-unit-law-algebra-monad-Precategory C T (hom-algebra-monad-Precategory f)
  unit-law-algebra-monad-Precategory f = pr1 (pr2 (pr2 f))

  mul-law-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    has-mul-law-algebra-monad-Precategory C T (hom-algebra-monad-Precategory f)
  mul-law-algebra-monad-Precategory f = pr2 (pr2 (pr2 f))
```
