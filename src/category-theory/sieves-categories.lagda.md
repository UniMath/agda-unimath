# Sieves in categories

```agda
module category-theory.sieves-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **sieve** `S` on an object `X` in a category `C` is a collection of morphisms into `X` which is closed under precomposition by arbitrary morphisms of `C`. In other words, for any morphism `f : Y → X` in `S` and any morphism `g : Z → Y` in `C`, the morphism `f ∘ g : Z → X` is in `S`.

The notion of sieve generalizes simultaneously the notion of right ideal in a monoid (a one-object category) and a lower set in a poset (a category with at most one morphism between any two objects).

## Definition

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2) (A : obj-Cat C)
  where

  is-sieve-cat-Prop :
    {l3 : Level} (S : (X Y : obj-Cat C) → subtype l3 (type-hom-Cat C X Y)) →
    Prop (l1 ⊔ l2 ⊔ l3)
  is-sieve-cat-Prop S =
    Π-Prop
      ( obj-Cat C)
      ( λ X →
        Π-Prop
          ( obj-Cat C)
          ( λ Y →
            Π-Prop
              ( obj-Cat C)
              ( λ Z →
                Π-Prop
                  ( type-subtype (S Y X))
                  ( λ f →
                    Π-Prop
                      ( type-hom-Cat C Z Y)
                      ( λ g →
                        S Z X
                          (comp-hom-Cat C (inclusion-subtype (S Y X) f) g))))))

  is-sieve-Cat :
    {l3 : Level} (S : (X Y : obj-Cat C) → subtype l3 (type-hom-Cat C X Y)) →
    UU (l1 ⊔ l2 ⊔ l3)
  is-sieve-Cat S = type-Prop (is-sieve-cat-Prop S)

  is-prop-is-sieve-Cat :
    {l3 : Level} (S : (X Y : obj-Cat C) → subtype l3 (type-hom-Cat C X Y)) →
    is-prop (is-sieve-Cat S)
  is-prop-is-sieve-Cat S = is-prop-type-Prop (is-sieve-cat-Prop S)
```
