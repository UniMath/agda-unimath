# Descent for sequential colimits

```agda
module synthetic-homotopy-theory.descent-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="sequential colimits" Agda=equiv-descent-data-family-cocone-sequential-diagram}}
of
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
characterizes type families over sequential colimits as
[descent data](synthetic-homotopy-theory.descent-data-sequential-colimits.md)
over the base
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md).

Given a sequential diagram `(A, a)` and a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) with
vertex `X`, there is a commuting triangle

```text
          cocone-map
  (X → 𝒰) ---------> cocone A 𝒰
           \       /
            \     /
             \   /
              ∨ ∨
         descent-data A .
```

From [univalence](foundation-core.univalence.md) it follows that the right map
is an equivalence. If `X` is a colimit of `A`, then we have that the top map is
an equivalence, which imples that the left map is an equivalence.

## Theorem

```agda
module _
  {l1 : Level} {A : sequential-diagram l1}
  where

  equiv-descent-data-cocone-sequential-diagram :
    {l2 : Level} →
    cocone-sequential-diagram A (UU l2) ≃
    descent-data-sequential-colimit A l2
  equiv-descent-data-cocone-sequential-diagram =
    equiv-tot
      ( λ B →
        equiv-Π-equiv-family
          ( λ n → equiv-Π-equiv-family (λ a → equiv-univalence)))

  descent-data-cocone-sequential-diagram :
    {l2 : Level} →
    cocone-sequential-diagram A (UU l2) →
    descent-data-sequential-colimit A l2
  descent-data-cocone-sequential-diagram =
    map-equiv equiv-descent-data-cocone-sequential-diagram

  is-equiv-descent-data-cocone-sequential-diagram :
    {l2 : Level} → is-equiv (descent-data-cocone-sequential-diagram {l2})
  is-equiv-descent-data-cocone-sequential-diagram =
    is-equiv-map-equiv equiv-descent-data-cocone-sequential-diagram

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  triangle-descent-data-family-cocone-sequential-diagram :
    {l3 : Level} →
    coherence-triangle-maps
      ( descent-data-family-cocone-sequential-diagram c)
      ( descent-data-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c {Y = UU l3})
  triangle-descent-data-family-cocone-sequential-diagram P =
    eq-pair-eq-fiber
      ( eq-binary-htpy _ _
        ( λ n a →
          inv
            ( compute-equiv-eq-ap
              ( coherence-cocone-sequential-diagram c n a))))

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  is-equiv-descent-data-family-cocone-sequential-diagram :
    is-equiv (descent-data-family-cocone-sequential-diagram c {l3})
  is-equiv-descent-data-family-cocone-sequential-diagram =
    is-equiv-left-map-triangle
      ( descent-data-family-cocone-sequential-diagram c)
      ( descent-data-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c)
      ( triangle-descent-data-family-cocone-sequential-diagram c)
      ( up-c (UU l3))
      ( is-equiv-descent-data-cocone-sequential-diagram)

  equiv-descent-data-family-cocone-sequential-diagram :
    (X → UU l3) ≃ descent-data-sequential-colimit A l3
  pr1 equiv-descent-data-family-cocone-sequential-diagram =
    descent-data-family-cocone-sequential-diagram c
  pr2 equiv-descent-data-family-cocone-sequential-diagram =
    is-equiv-descent-data-family-cocone-sequential-diagram

  family-cocone-descent-data-sequential-colimit :
    descent-data-sequential-colimit A l3 → (X → UU l3)
  family-cocone-descent-data-sequential-colimit =
    map-inv-equiv
      ( equiv-descent-data-family-cocone-sequential-diagram)
```
