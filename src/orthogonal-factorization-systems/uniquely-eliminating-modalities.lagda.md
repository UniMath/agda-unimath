# Uniquely eliminating modalities

```agda
module orthogonal-factorization-systems.uniquely-eliminating-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-subuniverses
```

</details>

## Idea

A **uniquely eliminating modality** is a _higher mode of logic_ defined in terms
of a monadic modal operator `○` satisfying a certain locality condition.

## Definition

```agda
is-uniquely-eliminating-modality :
  {l1 l2 : Level} {○ : modal-operator l1 l2} → modal-unit ○ → UU (lsuc l1 ⊔ l2)
is-uniquely-eliminating-modality {l1} {l2} {○} unit-○ =
  (X : UU l1) (P : ○ X → UU l1) → is-local-family (unit-○) (○ ∘ P)

uniquely-eliminating-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniquely-eliminating-modality l1 l2 =
  Σ ( modal-operator l1 l2)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( is-uniquely-eliminating-modality))
```

### Projections for uniquely eliminating modalities

```agda
module _
  {l1 l2 : Level} {○ : modal-operator l1 l2} {unit-○ : modal-unit ○}
  (is-uem-○ : is-uniquely-eliminating-modality unit-○)
  where

  modal-ind-is-uniquely-eliminating-modality :
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) → (x' : ○ X) → ○ (P x')
  modal-ind-is-uniquely-eliminating-modality X P =
    map-inv-is-equiv (is-uem-○ X P)

  modal-comp-is-uniquely-eliminating-modality :
    (X : UU l1) (P : ○ X → UU l1) (f : (x : X) → ○ (P (unit-○ x))) →
    (pr1 (pr1 (is-uem-○ X P)) f ∘ unit-○) ~ f
  modal-comp-is-uniquely-eliminating-modality X P =
    htpy-eq ∘ pr2 (pr1 (is-uem-○ X P))

module _
  {l1 l2 : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l1 l2)
  where

  modal-operator-uniquely-eliminating-modality : modal-operator l1 l2
  modal-operator-uniquely-eliminating-modality = ○

  modal-unit-uniquely-eliminating-modality : modal-unit ○
  modal-unit-uniquely-eliminating-modality = unit-○

  is-uniquely-eliminating-modality-uniquely-eliminating-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-modality-uniquely-eliminating-modality = is-uem-○
```

## Properties

### Being uniquely eliminating is a property

```agda
module _
  {l1 l2 : Level} {○ : modal-operator l1 l2} (unit-○ : modal-unit ○)
  where

  is-prop-is-uniquely-eliminating-modality :
    is-prop (is-uniquely-eliminating-modality unit-○)
  is-prop-is-uniquely-eliminating-modality =
    is-prop-Π λ X → is-prop-Π λ P → is-property-is-local-family unit-○ (○ ∘ P)

  is-uniquely-eliminating-modality-Prop : Prop (lsuc l1 ⊔ l2)
  pr1 is-uniquely-eliminating-modality-Prop =
    is-uniquely-eliminating-modality unit-○
  pr2 is-uniquely-eliminating-modality-Prop =
    is-prop-is-uniquely-eliminating-modality
```

### `○ X` is modal

```agda
module _
  {l : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l l)
  (X : UU l)
  where

  map-inv-unit-uniquely-eliminating-modality : ○ (○ X) → ○ X
  map-inv-unit-uniquely-eliminating-modality =
    modal-ind-is-uniquely-eliminating-modality is-uem-○ (○ X) (λ _ → X) id

  issec-unit-uniquely-eliminating-modality :
    (map-inv-unit-uniquely-eliminating-modality ∘ unit-○) ~ id
  issec-unit-uniquely-eliminating-modality =
    modal-comp-is-uniquely-eliminating-modality is-uem-○ (○ X) (λ _ → X) id

  isretr-unit-uniquely-eliminating-modality :
    (unit-○ ∘ map-inv-unit-uniquely-eliminating-modality) ~ id
  isretr-unit-uniquely-eliminating-modality =
    htpy-eq
      ( ap pr1
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-uem-○ (○ X) (λ _ → ○ X)) unit-○)
          ( unit-○ ∘ map-inv-unit-uniquely-eliminating-modality ,
            eq-htpy (ap unit-○ ∘ (issec-unit-uniquely-eliminating-modality)))
          ( id , refl)))

  is-modal-uniquely-eliminating-modality : is-modal unit-○ (○ X)
  is-modal-uniquely-eliminating-modality =
    is-equiv-has-inverse
      map-inv-unit-uniquely-eliminating-modality
      isretr-unit-uniquely-eliminating-modality
      issec-unit-uniquely-eliminating-modality
```

### Uniquely eliminating modalities are uniquely determined by their modal types

This can also be seen as characterizing the identity type of uniquely
eliminating modalities.

Suppose given two uniquely eliminating modalities ○ and ●. They are equal if and
only if they have the same modal types.

```agda
module _
  {l1 l2 : Level}
  where

  htpy-uniquely-eliminating-modality :
    (○ ● : uniquely-eliminating-modality l1 l2) → UU (lsuc l1 ⊔ l2)
  htpy-uniquely-eliminating-modality ○ ● =
    equiv-fam
      ( is-modal (modal-unit-uniquely-eliminating-modality ○))
      ( is-modal (modal-unit-uniquely-eliminating-modality ●))

  refl-htpy-uniquely-eliminating-modality :
    (○ : uniquely-eliminating-modality l1 l2) →
    htpy-uniquely-eliminating-modality ○ ○
  refl-htpy-uniquely-eliminating-modality ○ X = id-equiv

  htpy-eq-uniquely-eliminating-modality :
    (○ ● : uniquely-eliminating-modality l1 l2) →
    ○ ＝ ● → htpy-uniquely-eliminating-modality ○ ●
  htpy-eq-uniquely-eliminating-modality ○ .○ refl =
    refl-htpy-uniquely-eliminating-modality ○

  -- eq-htpy-uniquely-eliminating-modality :
  --   (○ ● : uniquely-eliminating-modality l1 l2) →
  --   htpy-uniquely-eliminating-modality ○ ● → ○ ＝ ●
  -- eq-htpy-uniquely-eliminating-modality ○ ● e = eq-pair-Σ (eq-htpy (λ X → {!   !})) {!   !}
```

### A uniquely eliminating modality determines a Σ-closed reflective subuniverse

```agda
module _
  {l : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l l)
  where

  -- is-reflective-subuniverse-uniquely-eliminating-modality :
  --   is-reflective-subuniverse unit-○ (is-modal-Prop unit-○)
  -- pr1 is-reflective-subuniverse-uniquely-eliminating-modality =
  --   is-modal-uniquely-eliminating-modality (○ , unit-○ , is-uem-○)
  -- pr2 is-reflective-subuniverse-uniquely-eliminating-modality =
  --   λ X is-modal-X Y → {! is-uem-○ ? ? !}
  -- -- X is modal, so X ≃ ○ X, now apply is-uem-○ to ○ X
  -- --TODO: can this be proven without univalence?
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.dependent-pair-closed-reflective-subuniverses.md)
- [Orthogonal factorization systems](orthogonal-factorization-systems.orthogonal-factorization-systems.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
