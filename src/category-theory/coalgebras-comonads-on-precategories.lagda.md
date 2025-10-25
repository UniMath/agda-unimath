# Coalgebras over comonads on precategories

```agda
module category-theory.coalgebras-comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.comonads-on-precategories
open import category-theory.functors-precategories
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

A
{{#concept "coalgebra" Disambiguation="over a comonad on a precategory" Agda=coalgebra-comonad-Precategory}}
over a [comonad](category-theory.comonads-on-precategories.md) `T` consists of
an object `A` and morphism `a : A → TA` satisfying two compatibility laws:

- **Counit law**: `ε_A ∘ a = id_A`
- **Comultiplication law**: `Ta ∘ a = δ ∘ a`

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  {A : obj-Precategory C}
  (a : hom-Precategory C A (obj-endofunctor-comonad-Precategory C T A))
  where

  has-counit-law-coalgebra-comonad-Precategory : UU l2
  has-counit-law-coalgebra-comonad-Precategory =
    comp-hom-Precategory C (hom-counit-comonad-Precategory C T A) a ＝
    id-hom-Precategory C

  has-comul-law-coalgebra-comonad-Precategory : UU l2
  has-comul-law-coalgebra-comonad-Precategory =
    comp-hom-Precategory C (hom-endofunctor-comonad-Precategory C T a) a ＝
    comp-hom-Precategory C (hom-comul-comonad-Precategory C T A) a

  is-coalgebra-comonad-Precategory : UU l2
  is-coalgebra-comonad-Precategory =
    has-counit-law-coalgebra-comonad-Precategory ×
    has-comul-law-coalgebra-comonad-Precategory

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  coalgebra-comonad-Precategory : UU (l1 ⊔ l2)
  coalgebra-comonad-Precategory =
    Σ ( obj-Precategory C)
      ( λ A →
        Σ ( hom-Precategory C A (obj-endofunctor-comonad-Precategory C T A))
          ( λ a → is-coalgebra-comonad-Precategory C T a))

  obj-coalgebra-comonad-Precategory :
    coalgebra-comonad-Precategory → obj-Precategory C
  obj-coalgebra-comonad-Precategory = pr1

  hom-coalgebra-comonad-Precategory :
    (f : coalgebra-comonad-Precategory) →
    hom-Precategory C
      ( obj-coalgebra-comonad-Precategory f)
      ( obj-endofunctor-comonad-Precategory C T
        ( obj-coalgebra-comonad-Precategory f))
  hom-coalgebra-comonad-Precategory f = pr1 (pr2 f)

  comm-coalgebra-comonad-Precategory :
    (f : coalgebra-comonad-Precategory) →
    is-coalgebra-comonad-Precategory C T (hom-coalgebra-comonad-Precategory f)
  comm-coalgebra-comonad-Precategory f = pr2 (pr2 f)

  counit-law-coalgebra-comonad-Precategory :
    (f : coalgebra-comonad-Precategory) →
    has-counit-law-coalgebra-comonad-Precategory C T
      ( hom-coalgebra-comonad-Precategory f)
  counit-law-coalgebra-comonad-Precategory f = pr1 (pr2 (pr2 f))

  comul-law-coalgebra-comonad-Precategory :
    (f : coalgebra-comonad-Precategory) →
    has-comul-law-coalgebra-comonad-Precategory C T
      ( hom-coalgebra-comonad-Precategory f)
  comul-law-coalgebra-comonad-Precategory f = pr2 (pr2 (pr2 f))
```
