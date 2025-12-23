# Retracts of types

```agda
module foundation.retracts-of-types where

open import foundation-core.retracts-of-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.logical-equivalences
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

We say that a type `A` is a
{{#concept "retract" Disambiguation="of types" Agda=retract}} of a type `B` if
the types `A` and `B` come equipped with
{{#concept "retract data" Disambiguation="of types" Agda=retract}}, i.e., with
maps

```text
      i        r
  A -----> B -----> A
```

such that `r` is a [retraction](foundation-core.retractions.md) of `i`, i.e.,
there is a [homotopy](foundation-core.homotopies.md) `r ∘ i ~ id`. The map `i`
is called the **inclusion** of the retract data, and the map `r` is called the
**underlying map of the retraction**.

## Properties

### Characterizing equality of retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-htpy-retract :
    (R S : A retract-of B)
    (I : inclusion-retract R ~ inclusion-retract S)
    (H : map-retraction-retract R ~ map-retraction-retract S) →
    UU l1
  coherence-htpy-retract R S I H =
    ( is-retraction-map-retraction-retract R) ~
    ( horizontal-concat-htpy H I ∙h is-retraction-map-retraction-retract S)

  htpy-retract : (R S : A retract-of B) → UU (l1 ⊔ l2)
  htpy-retract R S =
    Σ ( inclusion-retract R ~ inclusion-retract S)
      ( λ I →
        Σ ( map-retraction-retract R ~ map-retraction-retract S)
          ( coherence-htpy-retract R S I))

  refl-htpy-retract : (R : A retract-of B) → htpy-retract R R
  refl-htpy-retract R = (refl-htpy , refl-htpy , refl-htpy)

  htpy-eq-retract : (R S : A retract-of B) → R ＝ S → htpy-retract R S
  htpy-eq-retract R .R refl = refl-htpy-retract R

  is-torsorial-htpy-retract :
    (R : A retract-of B) → is-torsorial (htpy-retract R)
  is-torsorial-htpy-retract R =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (inclusion-retract R))
      ( inclusion-retract R , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-retraction-retract R))
        ( map-retraction-retract R , refl-htpy)
        ( is-torsorial-htpy (is-retraction-map-retraction-retract R)))

  is-equiv-htpy-eq-retract :
    (R S : A retract-of B) → is-equiv (htpy-eq-retract R S)
  is-equiv-htpy-eq-retract R =
    fundamental-theorem-id (is-torsorial-htpy-retract R) (htpy-eq-retract R)

  extensionality-retract : (R S : A retract-of B) → (R ＝ S) ≃ htpy-retract R S
  extensionality-retract R S =
    ( htpy-eq-retract R S , is-equiv-htpy-eq-retract R S)

  eq-htpy-retract : (R S : A retract-of B) → htpy-retract R S → R ＝ S
  eq-htpy-retract R S = map-inv-is-equiv (is-equiv-htpy-eq-retract R S)
```

### Characterizing equality of the total type of retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-retracts :
    {l3 : Level} (R : retracts l2 A) (S : retracts l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-retracts R S =
    Σ ( type-retracts R ≃ type-retracts S)
      ( λ e →
        htpy-retract
          ( retract-retracts R)
          ( comp-retract (retract-retracts S) (retract-equiv e)))

  refl-equiv-retracts : (R : retracts l2 A) → equiv-retracts R R
  refl-equiv-retracts R =
    ( id-equiv ,
      refl-htpy ,
      refl-htpy ,
      ( ( inv-htpy
          ( left-unit-law-left-whisker-comp
            ( is-retraction-map-retraction-retracts R))) ∙h
        ( inv-htpy-right-unit-htpy)))

  equiv-eq-retracts : (R S : retracts l2 A) → R ＝ S → equiv-retracts R S
  equiv-eq-retracts R .R refl = refl-equiv-retracts R

  is-torsorial-equiv-retracts :
    (R : retracts l2 A) → is-torsorial (equiv-retracts R)
  is-torsorial-equiv-retracts R =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-retracts R))
      ( type-retracts R , id-equiv)
      ( is-contr-equiv
        ( Σ (retract A (type-retracts R)) (htpy-retract (retract-retracts R)))
        ( equiv-tot
          ( λ S →
            equiv-tot
              ( λ I →
                equiv-tot
                  ( λ J →
                    equiv-concat-htpy'
                      ( is-retraction-map-retraction-retracts R)
                      ( ap-concat-htpy
                        ( horizontal-concat-htpy J I)
                        ( right-unit-htpy ∙h
                          left-unit-law-left-whisker-comp
                            ( is-retraction-map-retraction-retract S)))))))
        ( is-torsorial-htpy-retract (retract-retracts R)))

  is-equiv-equiv-eq-retracts :
    (R S : retracts l2 A) → is-equiv (equiv-eq-retracts R S)
  is-equiv-equiv-eq-retracts R =
    fundamental-theorem-id (is-torsorial-equiv-retracts R) (equiv-eq-retracts R)

  extensionality-retracts : (R S : retracts l2 A) → (R ＝ S) ≃ equiv-retracts R S
  extensionality-retracts R S =
    ( equiv-eq-retracts R S , is-equiv-equiv-eq-retracts R S)

  eq-equiv-retracts : (R S : retracts l2 A) → equiv-retracts R S → R ＝ S
  eq-equiv-retracts R S = map-inv-is-equiv (is-equiv-equiv-eq-retracts R S)
```

### The underlying logical equivalence associated to a retract

```agda
iff-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B → A ↔ B
iff-retract R = inclusion-retract R , map-retraction-retract R

iff-retract' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B → B ↔ A
iff-retract' = inv-iff ∘ iff-retract
```

## See also

- [Retracts of arrows](foundation.retracts-of-arrows.md)
- [Retractive types](structured-types.retractive-types.md)
