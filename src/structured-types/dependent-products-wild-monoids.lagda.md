# Dependent products of wild monoids

```agda
module structured-types.dependent-products-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.dependent-products-h-spaces
open import structured-types.h-spaces
open import structured-types.pointed-types
open import structured-types.wild-monoids
```

</details>

## Idea

Given a family of [wild monoids](structured-types.wild-monoids.md) `Mᵢ` indexed
by `i : I`, the
{{#concept "dependent product" Disambiguation="wild monoid" Agda=Π-Wild-Monoid}}
`Π(i : I), Mᵢ` is a wild monoid consisting of dependent functions taking `i : I`
to an element of the underlying type of `Mᵢ`. Every component of the structure
is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Wild-Monoid l2)
  where

  h-space-Π-Wild-Monoid : H-Space (l1 ⊔ l2)
  h-space-Π-Wild-Monoid =
    Π-H-Space I (λ i → h-space-Wild-Monoid (M i))

  pointed-type-Π-Wild-Monoid : Pointed-Type (l1 ⊔ l2)
  pointed-type-Π-Wild-Monoid =
    pointed-type-H-Space h-space-Π-Wild-Monoid

  type-Π-Wild-Monoid : UU (l1 ⊔ l2)
  type-Π-Wild-Monoid = type-H-Space h-space-Π-Wild-Monoid

  unit-Π-Wild-Monoid : type-Π-Wild-Monoid
  unit-Π-Wild-Monoid = unit-H-Space h-space-Π-Wild-Monoid

  mul-Π-Wild-Monoid :
    type-Π-Wild-Monoid → type-Π-Wild-Monoid → type-Π-Wild-Monoid
  mul-Π-Wild-Monoid = mul-H-Space h-space-Π-Wild-Monoid

  left-unit-law-mul-Π-Wild-Monoid :
    (f : type-Π-Wild-Monoid) → (mul-Π-Wild-Monoid (unit-Π-Wild-Monoid) f) ＝ f
  left-unit-law-mul-Π-Wild-Monoid =
    left-unit-law-mul-H-Space h-space-Π-Wild-Monoid

  right-unit-law-mul-Π-Wild-Monoid :
    (f : type-Π-Wild-Monoid) → (mul-Π-Wild-Monoid f (unit-Π-Wild-Monoid)) ＝ f
  right-unit-law-mul-Π-Wild-Monoid =
    right-unit-law-mul-H-Space h-space-Π-Wild-Monoid

  associator-Π-Wild-Monoid :
    associator-H-Space h-space-Π-Wild-Monoid
  associator-Π-Wild-Monoid f g h =
    eq-htpy (λ i → associator-Wild-Monoid (M i) (f i) (g i) (h i))

  unital-associator-Π-Wild-Monoid :
    unital-associator h-space-Π-Wild-Monoid
  pr1 unital-associator-Π-Wild-Monoid = associator-Π-Wild-Monoid
  pr1 (pr2 unital-associator-Π-Wild-Monoid) g h =
    ( inv
      ( eq-htpy-concat-htpy
        ( λ i → associator-Wild-Monoid (M i) (unit-Π-Wild-Monoid i) (g i) (h i))
        ( λ i →
          left-unit-law-mul-Wild-Monoid (M i) (mul-Π-Wild-Monoid g h i)))) ∙
    ( ap
      ( eq-htpy)
      ( eq-htpy
        ( λ i →
          pr1 (pr2 (unital-associator-Wild-Monoid (M i))) (g i) (h i)))) ∙
    ( compute-eq-htpy-ap (λ i → left-unit-law-mul-Wild-Monoid (M i) (g i)))
  pr1 (pr2 (pr2 unital-associator-Π-Wild-Monoid)) f h =
    ( ap
      ( associator-Π-Wild-Monoid f unit-Π-Wild-Monoid h ∙_)
      ( inv
        ( compute-eq-htpy-ap
          ( λ i → left-unit-law-mul-Wild-Monoid (M i) (h i))))) ∙
    ( inv
      ( eq-htpy-concat-htpy
        ( λ i →
          associator-Wild-Monoid (M i) (f i) (unit-Π-Wild-Monoid i) (h i))
        ( λ i →
          ap
            ( mul-Wild-Monoid (M i) (f i))
            ( left-unit-law-mul-Wild-Monoid (M i) (h i))))) ∙
    ( ap
      ( eq-htpy)
      ( eq-htpy
        ( λ i →
          pr1 (pr2 (pr2 (unital-associator-Wild-Monoid (M i)))) (f i) (h i)))) ∙
    ( compute-eq-htpy-ap (λ i → right-unit-law-mul-Wild-Monoid (M i) (f i)))
  pr1 (pr2 (pr2 (pr2 unital-associator-Π-Wild-Monoid))) f g =
    ( ap
      ( associator-Π-Wild-Monoid f g unit-Π-Wild-Monoid ∙_)
      ( inv
        ( compute-eq-htpy-ap
          ( λ i → right-unit-law-mul-Wild-Monoid (M i) (g i))))) ∙
    ( inv
      ( eq-htpy-concat-htpy
        ( λ i → associator-Wild-Monoid (M i) (f i) (g i) (unit-Π-Wild-Monoid i))
        ( λ i →
          ap
            ( mul-Wild-Monoid (M i) (f i))
            ( right-unit-law-mul-Wild-Monoid (M i) (g i))))) ∙
    ( ap
      ( eq-htpy)
      ( eq-htpy
        ( λ i →
          pr1
            ( pr2 (pr2 (pr2 (unital-associator-Wild-Monoid (M i)))))
            ( f i)
            ( g i))))
  pr2 (pr2 (pr2 (pr2 unital-associator-Π-Wild-Monoid))) = star

  Π-Wild-Monoid : Wild-Monoid (l1 ⊔ l2)
  pr1 Π-Wild-Monoid = h-space-Π-Wild-Monoid
  pr2 Π-Wild-Monoid = unital-associator-Π-Wild-Monoid
```
