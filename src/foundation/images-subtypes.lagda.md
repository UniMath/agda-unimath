# Images of subtypes

```agda
module foundation.images-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

Consider a map `f : A → B` and a subtype `S ⊆ A`, then the images of `S` under `f` is the subtype of `B` consisting of the values of the composite `S ⊆ A → B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  subtype-im-subtype :
    {l3 : Level} → subtype l3 A → subtype (l1 ⊔ l2 ⊔ l3) B
  subtype-im-subtype S y = subtype-im (f ∘ inclusion-subtype S) y
```

## Properties

If now `f` is an equivalence between `A` and `B`, then there is an equivalence between `S` and the image of `S` by `f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ≃ B)
  where

  equiv-type-subtype-im-subtype :
    {l3 : Level} → (S : subtype l3 A) →
    type-subtype S ≃ type-subtype (subtype-im-subtype (map-equiv f) S)
  pr1 (equiv-type-subtype-im-subtype S) (a , S-a) =
    ( map-equiv f a ,
      unit-trunc-Prop ((a , S-a) , refl))
  pr2 (equiv-type-subtype-im-subtype S) =
    is-equiv-has-inverse
      ( λ x →
        ( map-inv-equiv f (pr1 x)) ,
          ( apply-universal-property-trunc-Prop
            ( pr2 x)
            ( S (map-inv-equiv f (pr1 x)))
            ( λ y →
              map-equiv
                ( equiv-eq
                  ( ap
                    ( λ x → type-Prop (S x))
                    ( map-eq-transpose-equiv f ( pr2 y))))
                ( pr2 (pr1 y)))))
      ( λ y →
        eq-type-subtype
          ( subtype-im-subtype (map-equiv f) S)
          ( issec-map-inv-equiv f (pr1 y)))
      ( λ x →
        eq-type-subtype
        ( S)
        ( isretr-map-inv-equiv f (pr1 x)))
```
