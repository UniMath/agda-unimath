# Equivalences of cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-prisms-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Consider two
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md) `(A, a)`
and `(B, b)`, equipped with
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c : A → X` and `c' : B → Y`, respectively, and an
[equivalence of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md)
`e : A ≃ B`. Then an
{{#concept "equivalence of cocones" Disambiguation="under an equivalence of sequential diagrams" Agda=equiv-cocone-equiv-sequential-diagram}}
under `e` is a triple `(u, H, K)`, with `u : X ≃ Y` a map of vertices of the
coforks, `H` a family of [homotopies](foundation-core.homotopies.md) witnessing
that the square

```text
           iₙ
     Aₙ -------> X
     |           |
  hₙ | ≃       ≃ | u
     |           |
     ∨           ∨
     Bₙ -------> Y
           i'ₙ
```

[commutes](foundation-core.commuting-squares-of-maps.md) for every `n`, and `K`
a family of coherence data filling the insides of the resulting
[prism](foundation.commuting-prisms-of-maps.md) boundaries

```text
            Aₙ₊₁
       aₙ  ∧ |  \  iₙ₊₁
         /   |    \
       /     |      ∨
     Aₙ -----------> X
     |   iₙ  |       |
     |       | hₙ₊₁  |
  hₙ |       ∨       | u
     |      Bₙ₊₁     |
     |  bₙ ∧   \i'ₙ₊₁|
     |   /       \   |
     ∨ /           ∨ ∨
     Bₙ -----------> Y
            i'ₙ
```

for every `n`.

## Definition

### Equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (e : equiv-sequential-diagram A B)
  where

  coherence-map-cocone-equiv-cocone-equiv-sequential-diagram :
    (X ≃ Y) → UU (l1 ⊔ l4)
  coherence-map-cocone-equiv-cocone-equiv-sequential-diagram u =
    (n : ℕ) →
    coherence-square-maps
      ( map-cocone-sequential-diagram c n)
      ( map-equiv-sequential-diagram B e n)
      ( map-equiv u)
      ( map-cocone-sequential-diagram c' n)

  coherence-equiv-cocone-equiv-sequential-diagram :
    (u : X ≃ Y) →
    coherence-map-cocone-equiv-cocone-equiv-sequential-diagram u →
    UU (l1 ⊔ l4)
  coherence-equiv-cocone-equiv-sequential-diagram u H =
    (n : ℕ) →
    vertical-coherence-prism-maps
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-sequential-diagram c' n)
      ( map-cocone-sequential-diagram c' (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-equiv-sequential-diagram B e n)
      ( map-equiv-sequential-diagram B e (succ-ℕ n))
      ( map-equiv u)
      ( coherence-cocone-sequential-diagram c n)
      ( H n)
      ( H (succ-ℕ n))
      ( naturality-equiv-sequential-diagram B e n)
      ( coherence-cocone-sequential-diagram c' n)

  equiv-cocone-equiv-sequential-diagram : UU (l1 ⊔ l2 ⊔ l4)
  equiv-cocone-equiv-sequential-diagram =
    Σ ( X ≃ Y)
      ( λ u →
        Σ ( coherence-map-cocone-equiv-cocone-equiv-sequential-diagram u)
          ( coherence-equiv-cocone-equiv-sequential-diagram u))

  module _
    (e' : equiv-cocone-equiv-sequential-diagram)
    where

    equiv-equiv-cocone-equiv-sequential-diagram : X ≃ Y
    equiv-equiv-cocone-equiv-sequential-diagram = pr1 e'

    map-equiv-cocone-equiv-sequential-diagram : X → Y
    map-equiv-cocone-equiv-sequential-diagram =
      map-equiv equiv-equiv-cocone-equiv-sequential-diagram

    is-equiv-map-equiv-cocone-equiv-sequential-diagram :
      is-equiv map-equiv-cocone-equiv-sequential-diagram
    is-equiv-map-equiv-cocone-equiv-sequential-diagram =
      is-equiv-map-equiv equiv-equiv-cocone-equiv-sequential-diagram

    coh-map-cocone-equiv-cocone-equiv-sequential-diagram :
      coherence-map-cocone-equiv-cocone-equiv-sequential-diagram
        ( equiv-equiv-cocone-equiv-sequential-diagram)
    coh-map-cocone-equiv-cocone-equiv-sequential-diagram = pr1 (pr2 e')

    coh-equiv-cocone-equiv-sequential-diagram :
      coherence-equiv-cocone-equiv-sequential-diagram
        ( equiv-equiv-cocone-equiv-sequential-diagram)
        ( coh-map-cocone-equiv-cocone-equiv-sequential-diagram)
    coh-equiv-cocone-equiv-sequential-diagram = pr2 (pr2 e')

    hom-equiv-cocone-equiv-sequential-diagram :
      hom-cocone-hom-sequential-diagram c c'
        ( hom-equiv-sequential-diagram B e)
    pr1 hom-equiv-cocone-equiv-sequential-diagram =
      map-equiv-cocone-equiv-sequential-diagram
    pr1 (pr2 hom-equiv-cocone-equiv-sequential-diagram) =
      coh-map-cocone-equiv-cocone-equiv-sequential-diagram
    pr2 (pr2 hom-equiv-cocone-equiv-sequential-diagram) =
      coh-equiv-cocone-equiv-sequential-diagram
```

### The predicate on morphisms of cocones under equivalences of sequential diagrams of being an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (e : equiv-sequential-diagram A B)
  where

  is-equiv-hom-cocone-equiv-sequential-diagram :
    hom-cocone-hom-sequential-diagram c c' (hom-equiv-sequential-diagram B e) →
    UU (l2 ⊔ l4)
  is-equiv-hom-cocone-equiv-sequential-diagram h =
    is-equiv (map-hom-cocone-hom-sequential-diagram c c' h)

  is-equiv-hom-equiv-cocone-equiv-sequential-diagram :
    (e' : equiv-cocone-equiv-sequential-diagram c c' e) →
    is-equiv-hom-cocone-equiv-sequential-diagram
      ( hom-equiv-cocone-equiv-sequential-diagram c c' e e')
  is-equiv-hom-equiv-cocone-equiv-sequential-diagram e' =
    is-equiv-map-equiv-cocone-equiv-sequential-diagram c c' e e'
```

## Properties

### Morphisms of cocones under equivalences of arrows which are equivalences are equivalences of cocones

To construct an equivalence of cocones under an equivalence `e` of sequential
diagrams, it suffices to construct a morphism of cocones under the underlying
morphism of sequential diagrams of `e`, and show that the map `X → Y` is an
equivalence.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (e : equiv-sequential-diagram A B)
  where

  equiv-hom-cocone-equiv-sequential-diagram :
    (h :
      hom-cocone-hom-sequential-diagram c c'
        ( hom-equiv-sequential-diagram B e)) →
    is-equiv-hom-cocone-equiv-sequential-diagram c c' e h →
    equiv-cocone-equiv-sequential-diagram c c' e
  pr1 (equiv-hom-cocone-equiv-sequential-diagram h is-equiv-map-cocone) =
    (map-hom-cocone-hom-sequential-diagram c c' h , is-equiv-map-cocone)
  pr1 (pr2 (equiv-hom-cocone-equiv-sequential-diagram h _)) =
    coh-map-cocone-hom-cocone-hom-sequential-diagram c c' h
  pr2 (pr2 (equiv-hom-cocone-equiv-sequential-diagram h _)) =
    coh-hom-cocone-hom-sequential-diagram c c' h
```
