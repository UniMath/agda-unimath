# Equivalences of coforks

```agda
module synthetic-homotopy-theory.equivalences-coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
```

</details>

## Idea

TODO

## Definitions

### Equivalences of coforks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (e : equiv-double-arrow a a')
  where

  coherence-equiv-cofork : (X ≃ Y) → UU (l2 ⊔ l6)
  coherence-equiv-cofork u =
    coherence-square-maps'
      ( map-cofork a c)
      ( codomain-map-equiv-double-arrow a a' e)
      ( map-equiv u)
      ( map-cofork a' c')

  coherence-equiv-cofork' :
    (u : X ≃ Y) → coherence-equiv-cofork u →
    UU (l1 ⊔ l6)
  coherence-equiv-cofork' u H =
    ( ( H ·r (bottom-map-double-arrow a)) ∙h
      ( ( map-cofork a' c') ·l
        ( bottom-coherence-square-equiv-double-arrow a a' e)) ∙h
      ( (coh-cofork a' c') ·r (domain-map-equiv-double-arrow a a' e))) ~
    ( ( (map-equiv u) ·l (coh-cofork a c)) ∙h
      ( H ·r (top-map-double-arrow a)) ∙h
      ( (map-cofork a' c') ·l (top-coherence-square-equiv-double-arrow a a' e)))

  equiv-cofork : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  equiv-cofork =
    Σ ( X ≃ Y)
      ( λ u →
        Σ ( coherence-equiv-cofork u)
          ( coherence-equiv-cofork' u))

  module _
    (e' : equiv-cofork)
    where

    equiv-equiv-cofork : X ≃ Y
    equiv-equiv-cofork = pr1 e'

    map-equiv-cofork : X → Y
    map-equiv-cofork = map-equiv equiv-equiv-cofork

    is-equiv-map-equiv-cofork : is-equiv map-equiv-cofork
    is-equiv-map-equiv-cofork =
      is-equiv-map-equiv equiv-equiv-cofork

    coh-equiv-cofork : coherence-equiv-cofork equiv-equiv-cofork
    coh-equiv-cofork = pr1 (pr2 e')

    coh-equiv-cofork' :
      coherence-equiv-cofork' equiv-equiv-cofork coh-equiv-cofork
    coh-equiv-cofork' = pr2 (pr2 e')
```
