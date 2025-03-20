# Morphisms of cocones under morphisms of sequential diagrams

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-prisms-of-maps funext
open import foundation.commuting-squares-of-maps funext
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams funext
open import synthetic-homotopy-theory.morphisms-sequential-diagrams funext
open import synthetic-homotopy-theory.sequential-diagrams funext
```

</details>

## Idea

Consider two
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md) `(A, a)`
and `(B, b)`, equipped with
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c : A → X` and `c' : B → Y`, respectively, and a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`h : A → B`. Then a
{{#concept "morphism of cocones" Disambiguation="under a morphism of sequential diagrams" Agda=hom-cocone-hom-sequential-diagram}}
under `h` is a triple `(u, H, K)`, with `u : X → Y` a map of vertices of the
coforks, `H` a family of [homotopies](foundation-core.homotopies.md) witnessing
that the square

```text
           iₙ
     Aₙ -------> X
     |           |
  hₙ |           | u
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

### Morphisms of cocones under morphisms of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (h : hom-sequential-diagram A B)
  where

  coherence-map-cocone-hom-cocone-hom-sequential-diagram :
    (X → Y) → UU (l1 ⊔ l4)
  coherence-map-cocone-hom-cocone-hom-sequential-diagram u =
    (n : ℕ) →
    coherence-square-maps
      ( map-cocone-sequential-diagram c n)
      ( map-hom-sequential-diagram B h n)
      ( u)
      ( map-cocone-sequential-diagram c' n)

  coherence-hom-cocone-hom-sequential-diagram :
    (u : X → Y) →
    coherence-map-cocone-hom-cocone-hom-sequential-diagram u →
    UU (l1 ⊔ l4)
  coherence-hom-cocone-hom-sequential-diagram u H =
    (n : ℕ) →
    vertical-coherence-prism-maps
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-sequential-diagram c' n)
      ( map-cocone-sequential-diagram c' (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B h n)
      ( map-hom-sequential-diagram B h (succ-ℕ n))
      ( u)
      ( coherence-cocone-sequential-diagram c n)
      ( H n)
      ( H (succ-ℕ n))
      ( naturality-map-hom-sequential-diagram B h n)
      ( coherence-cocone-sequential-diagram c' n)

  hom-cocone-hom-sequential-diagram : UU (l1 ⊔ l2 ⊔ l4)
  hom-cocone-hom-sequential-diagram =
    Σ ( X → Y)
      ( λ u →
        Σ ( coherence-map-cocone-hom-cocone-hom-sequential-diagram u)
          ( coherence-hom-cocone-hom-sequential-diagram u))
```

### Components of a morphism of cocones under a morphism of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  {h : hom-sequential-diagram A B}
  (m : hom-cocone-hom-sequential-diagram c c' h)
  where

  map-hom-cocone-hom-sequential-diagram : X → Y
  map-hom-cocone-hom-sequential-diagram = pr1 m

  coh-map-cocone-hom-cocone-hom-sequential-diagram :
    coherence-map-cocone-hom-cocone-hom-sequential-diagram c c' h
      ( map-hom-cocone-hom-sequential-diagram)
  coh-map-cocone-hom-cocone-hom-sequential-diagram = pr1 (pr2 m)

  coh-hom-cocone-hom-sequential-diagram :
    coherence-hom-cocone-hom-sequential-diagram c c' h
      ( map-hom-cocone-hom-sequential-diagram)
      ( coh-map-cocone-hom-cocone-hom-sequential-diagram)
  coh-hom-cocone-hom-sequential-diagram = pr2 (pr2 m)
```
