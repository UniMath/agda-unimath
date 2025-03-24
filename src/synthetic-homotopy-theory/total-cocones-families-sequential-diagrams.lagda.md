# Total cocones of type families over cocones under sequential diagrams

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.total-cocones-families-sequential-diagrams
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types funext
open import foundation.equivalences funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation funext

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams funext univalence truncations
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams funext univalence truncations
open import synthetic-homotopy-theory.equivalences-sequential-diagrams funext univalence truncations
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits funext univalence truncations
open import synthetic-homotopy-theory.sequential-diagrams funext univalence
open import synthetic-homotopy-theory.total-sequential-diagrams funext univalence truncations
```

</details>

## Idea

Given a sequential diagram `(A, a)` and a cocone `c` under it with vertex `X`, a
type family `P : X → 𝒰` induces a dependent sequential diagram over `A`, as
shown in
[`cocones-under-sequential-diagrams`](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md).

Here we show that when `P` is additionally equipped with corresponding
[descent data](synthetic-homotopy-theory.families-descent-data-sequential-colimits.md)
`B`, it induces a cocone on the total sequential diagram

```text
  Σ A₀ B₀ ----> Σ A₁ B₁ ----> ⋯ ----> Σ X P .
```

Specializing the above to the case when the descent data is the one induced by
the family, we get a cocone of the form

```text
                tot₍₊₁₎ (tr P Hₙ)
  Σ Aₙ (P ∘ iₙ) ----------------> Σ Aₙ₊₁ (P ∘ iₙ₊₁)
                \               /
                  \           /
  map-Σ-map-base iₙ \       / map-Σ-map-base iₙ₊₁
                      \   /
                       ∨ ∨
                      Σ X P .
```

Furthermore, the two total diagrams are
[equivalent](synthetic-homotopy-theory.equivalences-sequential-diagrams.md), and
the two induced cocones are also
[equivalent](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.md)
under this equivalence.

## Definitions

### Cocones under total sequential diagrams induced by type families with descent data

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : family-with-descent-data-sequential-colimit c l3)
  where

  total-sequential-diagram-family-with-descent-data-sequential-colimit :
    sequential-diagram (l1 ⊔ l3)
  total-sequential-diagram-family-with-descent-data-sequential-colimit =
    total-sequential-diagram
      ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit
        ( P))

  total-cocone-family-with-descent-data-sequential-colimit :
    cocone-sequential-diagram
      ( total-sequential-diagram-family-with-descent-data-sequential-colimit)
      ( Σ X (family-cocone-family-with-descent-data-sequential-colimit P))
  pr1 total-cocone-family-with-descent-data-sequential-colimit n =
    map-Σ
      ( family-cocone-family-with-descent-data-sequential-colimit P)
      ( map-cocone-sequential-diagram c n)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit P n)
  pr2 total-cocone-family-with-descent-data-sequential-colimit n =
    coherence-triangle-maps-Σ
      ( family-cocone-family-with-descent-data-sequential-colimit P)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit P n)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit P
        ( succ-ℕ n))
      ( map-family-family-with-descent-data-sequential-colimit P n)
      ( λ a →
        inv-htpy
          ( coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimit
            ( P)
            ( n)
            ( a)))

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  (P : X → UU l3)
  where

  total-sequential-diagram-family-cocone-sequential-diagram :
    sequential-diagram (l1 ⊔ l3)
  total-sequential-diagram-family-cocone-sequential-diagram =
    total-sequential-diagram-family-with-descent-data-sequential-colimit
      ( family-with-descent-data-family-cocone-sequential-diagram c P)

  total-cocone-family-cocone-sequential-diagram :
    cocone-sequential-diagram
      ( total-sequential-diagram-family-cocone-sequential-diagram)
      ( Σ X P)
  total-cocone-family-cocone-sequential-diagram =
    total-cocone-family-with-descent-data-sequential-colimit
      ( family-with-descent-data-family-cocone-sequential-diagram c P)
```

### Type families with descent data for sequential colimits induce an equivalence between the cocone induced by descent data and the cocone induced by the family

In other words, there is an
[equivalence of cocones](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.md)
under the induced equivalence of sequential diagrams

```text
     Σ A₀ B₀ ---------> Σ A₁ B₁ ------> ⋯ -----> Σ X P
        |                  |                       |
        | ≃                | ≃                     | ≃
        ∨                  ∨                       ∨
  Σ A₀ (P ∘ i₀) ---> Σ A₁ (P ∘ i₁) ---> ⋯ -----> Σ X P .
```

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : family-with-descent-data-sequential-colimit c l3)
  where

  equiv-total-sequential-diagram-family-with-descent-data-sequential-colimit :
    equiv-sequential-diagram
      ( total-sequential-diagram-family-with-descent-data-sequential-colimit P)
      ( total-sequential-diagram-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit P))
  equiv-total-sequential-diagram-family-with-descent-data-sequential-colimit =
    equiv-total-sequential-diagram-equiv-dependent-sequential-diagram _
      ( dependent-sequential-diagram-family-cocone c
        ( family-cocone-family-with-descent-data-sequential-colimit P))
      ( equiv-descent-data-family-with-descent-data-sequential-colimit P)

  equiv-total-cocone-family-with-descent-data-sequential-colimit :
    equiv-cocone-equiv-sequential-diagram
      ( total-cocone-family-with-descent-data-sequential-colimit P)
      ( total-cocone-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit P))
      ( equiv-total-sequential-diagram-family-with-descent-data-sequential-colimit)
  pr1 equiv-total-cocone-family-with-descent-data-sequential-colimit =
    id-equiv
  pr1 (pr2 equiv-total-cocone-family-with-descent-data-sequential-colimit) n =
    refl-htpy
  pr2 (pr2 equiv-total-cocone-family-with-descent-data-sequential-colimit)
    n (a , b) =
    ( left-whisker-concat
      ( eq-pair-Σ (coherence-cocone-sequential-diagram c n a) refl)
      ( ( right-unit) ∙
        ( compute-ap-map-Σ-map-base-eq-pair-Σ _ _ _ _))) ∙
    ( inv
      ( ( ap-id _) ∙
        ( triangle-eq-pair-Σ
          ( family-cocone-family-with-descent-data-sequential-colimit P)
          ( coherence-cocone-sequential-diagram c n a)
          ( _))))
```
