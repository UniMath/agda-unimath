# Whiskering of pointed homotopies

```agda
module structured-types.whiskering-pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Consider a [pointed homotopy](structured-types.pointed-homotopies.md) `H : f ~∗ g` between [pointed maps](structured-types.pointed-maps.md) `f g : A →∗ B`, and consider a pointed map `h : B →∗ C`, as indicated in the diagram

```text
      f
    ----->     h
  A -----> B -----> C.
      g
```

The {{#concept "left whiskering operation on pointed homotopies"}} takes a pointed homotopy `H` and a pointed map `f` and returns a pointed homotopy

```text
  h ·l∗ H : h ∘∗ f ~∗ h ∘∗ g
```

## Definitions

### Left whiskering of pointed homotopies

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  left-whisker-htpy-pointed-map :
    (g : B →∗ C) (f1 f2 : A →∗ B) (H : htpy-pointed-map f1 f2) →
    htpy-pointed-map
      ( comp-pointed-map g f1)
      ( comp-pointed-map g f2)
  left-whisker-htpy-pointed-map g f1 f2 H =
    pair
      ( map-pointed-map g ·l (pr1 H))
      ( ( ( ( ap (ap (pr1 g)) (pr2 H)) ∙
            ( ap-concat (pr1 g) (pr2 f1) (inv (pr2 f2)))) ∙
          ( ap
            ( concat
              ( ap (pr1 g) (pr2 f1))
              ( map-pointed-map g
                ( map-pointed-map f2 (point-Pointed-Type A))))
            ( ( ( ( ap-inv (pr1 g) (pr2 f2)) ∙
                  ( ap
                    ( concat'
                      ( pr1 g (point-Pointed-Fam A (constant-Pointed-Fam A B)))
                      ( inv (ap (pr1 g) (pr2 f2)))))
                  ( inv (right-inv (pr2 g)))) ∙
                ( assoc
                  ( pr2 g)
                  ( inv (pr2 g))
                  ( inv (ap (pr1 g) (pr2 f2))))) ∙
              ( ap
                ( concat
                  ( pr2 g)
                  ( map-pointed-map g
                    ( map-pointed-map f2 (point-Pointed-Type A))))
                ( inv
                  ( distributive-inv-concat
                    ( ap (pr1 g) (pr2 f2))
                    ( pr2 g))))))) ∙
        ( inv
          ( assoc
            ( ap (pr1 g) (pr2 f1))
            ( pr2 g)
            ( inv (ap (pr1 g) (pr2 f2) ∙ pr2 g)))))
```

### Right whiskering of pointed homotopies

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  right-whisker-htpy-pointed-map :
    (g1 g2 : B →∗ C) (H : htpy-pointed-map g1 g2) (f : A →∗ B) →
    htpy-pointed-map (comp-pointed-map g1 f) (comp-pointed-map g2 f)
  right-whisker-htpy-pointed-map g1 g2 H (pair f refl) =
    pair (pr1 H ·r f) (pr2 H)
```
