# Morphisms of types equipped with endomorphisms

```agda
module structured-types.morphisms-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Definition

### Morphisms of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  hom-Endo : UU (l1 ⊔ l2)
  hom-Endo =
    Σ ( type-Endo X → type-Endo Y)
      ( λ f →
        coherence-square-maps f (endomorphism-Endo X) (endomorphism-Endo Y) f)

  map-hom-Endo : hom-Endo → type-Endo X → type-Endo Y
  map-hom-Endo = pr1

  coherence-square-hom-Endo :
    (f : hom-Endo) →
    coherence-square-maps
      ( map-hom-Endo f)
      ( endomorphism-Endo X)
      ( endomorphism-Endo Y)
      ( map-hom-Endo f)
  coherence-square-hom-Endo = pr2
```

### Homotopies of morphisms of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  htpy-hom-Endo : (f g : hom-Endo X Y) → UU (l1 ⊔ l2)
  htpy-hom-Endo f g =
    Σ ( map-hom-Endo X Y f ~ map-hom-Endo X Y g)
      ( λ H →
        ( (H ·r endomorphism-Endo X) ∙h coherence-square-hom-Endo X Y g) ~
        ( coherence-square-hom-Endo X Y f ∙h (endomorphism-Endo Y ·l H)))

  refl-htpy-hom-Endo : (f : hom-Endo X Y) → htpy-hom-Endo f f
  pr1 (refl-htpy-hom-Endo f) = refl-htpy
  pr2 (refl-htpy-hom-Endo f) = inv-htpy-right-unit-htpy

  htpy-eq-hom-Endo : (f g : hom-Endo X Y) → Id f g → htpy-hom-Endo f g
  htpy-eq-hom-Endo f .f refl = refl-htpy-hom-Endo f

  is-contr-total-htpy-hom-Endo :
    (f : hom-Endo X Y) → is-contr (Σ (hom-Endo X Y) (htpy-hom-Endo f))
  is-contr-total-htpy-hom-Endo f =
    is-contr-total-Eq-structure
      ( λ g G H →
        ( (H ·r endomorphism-Endo X) ∙h G) ~
        ( coherence-square-hom-Endo X Y f ∙h (endomorphism-Endo Y ·l H)))
      ( is-contr-total-htpy (map-hom-Endo X Y f))
      ( pair (map-hom-Endo X Y f) refl-htpy)
      ( is-contr-equiv
        ( Σ ( coherence-square-maps
              ( map-hom-Endo X Y f)
              ( endomorphism-Endo X)
              ( endomorphism-Endo Y)
              ( map-hom-Endo X Y f))
            ( λ H → H ~ coherence-square-hom-Endo X Y f))
        ( equiv-tot (λ H → equiv-concat-htpy' H right-unit-htpy))
        ( is-contr-total-htpy' (coherence-square-hom-Endo X Y f)))

  is-equiv-htpy-eq-hom-Endo :
    (f g : hom-Endo X Y) → is-equiv (htpy-eq-hom-Endo f g)
  is-equiv-htpy-eq-hom-Endo f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-Endo f)
      ( htpy-eq-hom-Endo f)

  extensionality-hom-Endo : (f g : hom-Endo X Y) → Id f g ≃ htpy-hom-Endo f g
  pr1 (extensionality-hom-Endo f g) = htpy-eq-hom-Endo f g
  pr2 (extensionality-hom-Endo f g) = is-equiv-htpy-eq-hom-Endo f g

  eq-htpy-hom-Endo : (f g : hom-Endo X Y) → htpy-hom-Endo f g → Id f g
  eq-htpy-hom-Endo f g = map-inv-equiv (extensionality-hom-Endo f g)
```
