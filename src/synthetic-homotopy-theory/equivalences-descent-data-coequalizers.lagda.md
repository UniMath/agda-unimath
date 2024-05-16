# Equivalences of descent data for coequalizers

```agda
module synthetic-homotopy-theory.equivalences-descent-data-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.morphisms-descent-data-coequalizers
```

</details>

## Idea

## Definitions

### Equivalences of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  where

  equiv-descent-data-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ l3 ⊔ l4)
  equiv-descent-data-coequalizer =
    Σ ( fam-equiv
        ( family-descent-data-coequalizer P)
        ( family-descent-data-coequalizer Q))
      ( λ e →
        (a : domain-double-arrow F) →
        coherence-square-maps
          ( map-equiv (e (left-map-double-arrow F a)))
          ( map-family-descent-data-coequalizer P a)
          ( map-family-descent-data-coequalizer Q a)
          ( map-equiv (e (right-map-double-arrow F a))))

  module _
    (e : equiv-descent-data-coequalizer)
    where

    equiv-equiv-descent-data-coequalizer :
      (b : codomain-double-arrow F) →
      family-descent-data-coequalizer P b ≃
      family-descent-data-coequalizer Q b
    equiv-equiv-descent-data-coequalizer = pr1 e

    map-equiv-descent-data-coequalizer :
      (b : codomain-double-arrow F) →
      family-descent-data-coequalizer P b →
      family-descent-data-coequalizer Q b
    map-equiv-descent-data-coequalizer =
      map-fam-equiv equiv-equiv-descent-data-coequalizer

    is-equiv-map-equiv-descent-data-coequalizer :
      (b : codomain-double-arrow F) →
      is-equiv (map-equiv-descent-data-coequalizer b)
    is-equiv-map-equiv-descent-data-coequalizer =
      is-equiv-map-fam-equiv equiv-equiv-descent-data-coequalizer

    coherence-equiv-descent-data-coequalizer :
      (a : domain-double-arrow F) →
      coherence-square-maps
        ( map-equiv-descent-data-coequalizer (left-map-double-arrow F a))
        ( map-family-descent-data-coequalizer P a)
        ( map-family-descent-data-coequalizer Q a)
        ( map-equiv-descent-data-coequalizer (right-map-double-arrow F a))
    coherence-equiv-descent-data-coequalizer = pr2 e

    hom-equiv-descent-data-coequalizer : hom-descent-data-coequalizer P Q
    pr1 hom-equiv-descent-data-coequalizer =
      map-equiv-descent-data-coequalizer
    pr2 hom-equiv-descent-data-coequalizer =
      coherence-equiv-descent-data-coequalizer
```

### The identity equivalence of descent data for coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  id-equiv-descent-data-coequalizer : equiv-descent-data-coequalizer P P
  pr1 id-equiv-descent-data-coequalizer b = id-equiv
  pr2 id-equiv-descent-data-coequalizer a = refl-htpy
```

### Inverses of equivalences of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {P : descent-data-coequalizer F l3}
  {Q : descent-data-coequalizer F l4}
  where

  inv-equiv-descent-data-coequalizer :
    equiv-descent-data-coequalizer P Q → equiv-descent-data-coequalizer Q P
  pr1 (inv-equiv-descent-data-coequalizer e) b =
    inv-equiv (equiv-equiv-descent-data-coequalizer P Q e b)
  pr2 (inv-equiv-descent-data-coequalizer e) a =
    horizontal-inv-equiv-coherence-square-maps
      ( equiv-equiv-descent-data-coequalizer P Q e (left-map-double-arrow F a))
      ( map-family-descent-data-coequalizer P a)
      ( map-family-descent-data-coequalizer Q a)
      ( equiv-equiv-descent-data-coequalizer P Q e (right-map-double-arrow F a))
      ( coherence-equiv-descent-data-coequalizer P Q e a)
```

## Properties

### Characterization of identity types of descent data for coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  equiv-eq-descent-data-coequalizer :
    (Q : descent-data-coequalizer F l3) →
    P ＝ Q → equiv-descent-data-coequalizer P Q
  equiv-eq-descent-data-coequalizer .P refl =
    id-equiv-descent-data-coequalizer P

  abstract
    is-torsorial-equiv-descent-data-coequalizer :
      is-torsorial (equiv-descent-data-coequalizer {l4 = l3} P)
    is-torsorial-equiv-descent-data-coequalizer =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ b → is-torsorial-equiv (family-descent-data-coequalizer P b)))
        ( family-descent-data-coequalizer P , λ b → id-equiv)
        ( is-torsorial-Eq-Π
          ( λ a →
            is-torsorial-htpy-equiv
              ( equiv-family-descent-data-coequalizer P a)))

    is-equiv-equiv-eq-descent-data-coequalizer :
      (Q : descent-data-coequalizer F l3) →
      is-equiv (equiv-eq-descent-data-coequalizer Q)
    is-equiv-equiv-eq-descent-data-coequalizer =
      fundamental-theorem-id
        ( is-torsorial-equiv-descent-data-coequalizer)
        ( equiv-eq-descent-data-coequalizer)

  extensionality-descent-data-coequalizer :
    (Q : descent-data-coequalizer F l3) →
    (P ＝ Q) ≃ equiv-descent-data-coequalizer P Q
  pr1 (extensionality-descent-data-coequalizer Q) =
    equiv-eq-descent-data-coequalizer Q
  pr2 (extensionality-descent-data-coequalizer Q) =
    is-equiv-equiv-eq-descent-data-coequalizer Q

  eq-equiv-descent-data-coequalizer :
    (Q : descent-data-coequalizer F l3) →
    equiv-descent-data-coequalizer P Q → P ＝ Q
  eq-equiv-descent-data-coequalizer Q =
    map-inv-equiv (extensionality-descent-data-coequalizer Q)
```

### Morphisms of descent data for coequalizers which are equivalences are equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {P : descent-data-coequalizer F l3}
  {Q : descent-data-coequalizer F l4}
  where

  equiv-hom-descent-data-coequalizer :
    (h : hom-descent-data-coequalizer P Q) →
    is-fiberwise-equiv (map-hom-descent-data-coequalizer P Q h) →
    equiv-descent-data-coequalizer P Q
  pr1 (equiv-hom-descent-data-coequalizer h is-equiv-map) b =
    map-hom-descent-data-coequalizer P Q h b , is-equiv-map b
  pr2 (equiv-hom-descent-data-coequalizer h _) =
    coherence-hom-descent-data-coequalizer P Q h
```
