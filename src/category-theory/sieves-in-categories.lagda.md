# Sieves in categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.sieves-in-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations

open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

A **sieve** `S` on an object `X` in a category `C` is a collection of morphisms
into `X` which is closed under precomposition by arbitrary morphisms of `C`. In
other words, for any morphism `f : Y → X` in `S` and any morphism `g : Z → Y` in
`C`, the morphism `f ∘ g : Z → X` is in `S`.

The notion of sieve generalizes simultaneously the notion of right ideal in a
monoid (a one-object category) and a lower set in a poset (a category with at
most one morphism between any two objects).

## Definition

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (A : obj-Category C)
  where

  is-sieve-prop-Category :
    { l3 : Level}
    ( S : (X Y : obj-Category C) →
    subtype l3 (hom-Category C X Y)) → Prop (l1 ⊔ l2 ⊔ l3)
  is-sieve-prop-Category S =
    Π-Prop
      ( obj-Category C)
      ( λ X →
        Π-Prop
          ( obj-Category C)
          ( λ Y →
            Π-Prop
              ( obj-Category C)
              ( λ Z →
                Π-Prop
                  ( type-subtype (S Y X))
                  ( λ f →
                    Π-Prop
                      ( hom-Category C Z Y)
                      ( λ g →
                        S Z X
                          ( comp-hom-Category
                              C (inclusion-subtype (S Y X) f) g))))))

  is-sieve-Category :
    { l3 : Level}
    ( S : (X Y : obj-Category C) →
    subtype l3 (hom-Category C X Y)) → UU (l1 ⊔ l2 ⊔ l3)
  is-sieve-Category S = type-Prop (is-sieve-prop-Category S)

  is-prop-is-sieve-Category :
    { l3 : Level}
    ( S : (X Y : obj-Category C) → subtype l3 (hom-Category C X Y)) →
    is-prop (is-sieve-Category S)
  is-prop-is-sieve-Category S = is-prop-type-Prop (is-sieve-prop-Category S)
```
