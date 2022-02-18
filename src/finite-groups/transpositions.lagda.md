# Transpositions


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.transpositions where

open import univalent-combinatorics
open import univalent-foundations public
```

## Idea

Transpositions are permutations of two elements

## Definitions

```agda
module _
  {l : Level} (X : UU l) (P : X → decidable-Prop lzero)
  (H : has-cardinality (Σ X (λ x → type-decidable-Prop (P x))) 2)
  where

  map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x))) → X
  map-transposition' x (inl p) =
    pr1 (map-equiv (swap-two-elements H) (pair x p))
  map-transposition' x (inr np) = x

  map-transposition : X → X
  map-transposition x =
    map-transposition' x (is-decidable-type-decidable-Prop (P x))

  is-involution-map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x)))
    (d' : is-decidable (type-decidable-Prop (P (map-transposition' x d)))) →
    Id (map-transposition' (map-transposition' x d) d') x
  is-involution-map-transposition' x (inl p) (inl p') =
    ( ap
      ( λ y → map-transposition' (map-transposition' x (inl p)) (inl y))
      ( eq-is-prop (pr1 (pr2 (P (map-transposition' x (inl p))))))) ∙
    ( ap pr1 (htpy-eq-equiv (is-involution-swap-two-elements H) (pair x p)))
  is-involution-map-transposition' x (inl p) (inr np') =
    ex-falso (np' (pr2 (map-equiv (swap-two-elements H) (pair x p))))
  is-involution-map-transposition' x (inr np) (inl p') = ex-falso (np p')
  is-involution-map-transposition' x (inr np) (inr np') = refl

  is-involution-map-transposition : (map-transposition ∘ map-transposition) ~ id
  is-involution-map-transposition x =
    is-involution-map-transposition' x
      ( is-decidable-type-decidable-Prop (P x))
      ( is-decidable-type-decidable-Prop
        ( P (map-transposition' x (is-decidable-type-decidable-Prop (P x)))))

  is-equiv-map-transposition : is-equiv map-transposition
  pr1 (pr1 is-equiv-map-transposition) = map-transposition
  pr2 (pr1 is-equiv-map-transposition) = is-involution-map-transposition
  pr1 (pr2 is-equiv-map-transposition) = map-transposition
  pr2 (pr2 is-equiv-map-transposition) = is-involution-map-transposition

  is-not-identity-map-transposition : Id map-transposition id → empty
  is-not-identity-map-transposition f =
    is-not-identity-swap-two-elements H
      ( eq-htpy-equiv
        ( λ { (pair x p) →
              eq-pair-Σ
                ( ( ap
                    ( map-transposition' x)
                    ( eq-is-prop
                      ( is-prop-is-decidable
                        ( is-prop-type-decidable-Prop (P x)))
                        { y =
                          is-decidable-type-decidable-Prop (P x)})) ∙
                  ( htpy-eq f x))
                ( eq-is-prop (is-prop-type-decidable-Prop (P x)))}))
```
