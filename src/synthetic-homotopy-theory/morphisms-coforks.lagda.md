# Morphisms of coforks

```agda
module synthetic-homotopy-theory.morphisms-coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.homotopies
open import foundation.morphisms-double-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
```

</details>

## Idea

TODO

## Definitions

### Morphisms of coforks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2) {X : UU l3} (c : cofork a X)
  (a' : double-arrow l4 l5) {Y : UU l6} (c' : cofork a' Y)
  (h : hom-double-arrow a a')
  where

  coherence-hom-cofork : (X → Y) → UU (l2 ⊔ l6)
  coherence-hom-cofork u =
    coherence-square-maps'
      ( map-cofork a c)
      ( codomain-map-hom-double-arrow a a' h)
      ( u)
      ( map-cofork a' c')

  coherence-hom-cofork' :
    (u : X → Y) → coherence-hom-cofork u →
    UU (l1 ⊔ l6)
  coherence-hom-cofork' u H =
    ( ( H ·r (bottom-map-double-arrow a)) ∙h
      ( ( map-cofork a' c') ·l
        ( bottom-coherence-square-hom-double-arrow a a' h)) ∙h
      ( (coh-cofork a' c') ·r (domain-map-hom-double-arrow a a' h))) ~
    ( ( u ·l (coh-cofork a c)) ∙h
      ( H ·r (top-map-double-arrow a)) ∙h
      ( (map-cofork a' c') ·l (top-coherence-square-hom-double-arrow a a' h)))

  hom-cofork : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  hom-cofork =
    Σ ( X → Y)
      ( λ u →
        Σ ( coherence-hom-cofork u)
          ( coherence-hom-cofork' u))
```
