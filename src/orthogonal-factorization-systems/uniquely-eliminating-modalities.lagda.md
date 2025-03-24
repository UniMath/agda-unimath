# Uniquely eliminating modalities

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems.uniquely-eliminating-modalities
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps funext
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.univalence funext univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators funext univalence truncations
open import orthogonal-factorization-systems.types-local-at-maps funext univalence truncations
```

</details>

## Idea

A **uniquely eliminating modality** is a _higher mode of logic_ defined in terms
of a monadic
[modal operator](orthogonal-factorization-systems.modal-operators.md) `○`
satisfying a certain
[locality](orthogonal-factorization-systems.types-local-at-maps.md) condition,
namely that dependent precomposition by the modal unit `unit-○` is an
equivalence for type families over types in the image of the operator:

```text
  - ∘ unit-○ : Π (x : ○ X) (○ (P x)) ≃ Π (x : X) (○ (P (unit-○ x)))
```

## Definition

```agda
is-uniquely-eliminating-modality :
  {l1 l2 : Level} {○ : operator-modality l1 l2} →
  unit-modality ○ → UU (lsuc l1 ⊔ l2)
is-uniquely-eliminating-modality {l1} {l2} {○} unit-○ =
  {X : UU l1} (P : ○ X → UU l1) → is-local-dependent-type (unit-○) (○ ∘ P)

uniquely-eliminating-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniquely-eliminating-modality l1 l2 =
  Σ ( operator-modality l1 l2)
    ( λ ○ →
      Σ ( unit-modality ○)
        ( is-uniquely-eliminating-modality))
```

### Components of a uniquely eliminating modality

```agda
module _
  {l1 l2 : Level} {○ : operator-modality l1 l2} {unit-○ : unit-modality ○}
  (is-uem-○ : is-uniquely-eliminating-modality unit-○)
  where

  ind-modality-is-uniquely-eliminating-modality :
    {X : UU l1} (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) → (x' : ○ X) → ○ (P x')
  ind-modality-is-uniquely-eliminating-modality P =
    map-inv-is-equiv (is-uem-○ P)

  compute-ind-modality-is-uniquely-eliminating-modality :
    {X : UU l1} (P : ○ X → UU l1) (f : (x : X) → ○ (P (unit-○ x))) →
    (pr1 (pr1 (is-uem-○ P)) f ∘ unit-○) ~ f
  compute-ind-modality-is-uniquely-eliminating-modality P =
    htpy-eq ∘ pr2 (pr1 (is-uem-○ P))

module _
  {l1 l2 : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l1 l2)
  where

  operator-modality-uniquely-eliminating-modality : operator-modality l1 l2
  operator-modality-uniquely-eliminating-modality = ○

  unit-modality-uniquely-eliminating-modality : unit-modality ○
  unit-modality-uniquely-eliminating-modality = unit-○

  is-uniquely-eliminating-modality-uniquely-eliminating-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-modality-uniquely-eliminating-modality = is-uem-○
```

## Properties

### Being uniquely eliminating is a property

```agda
module _
  {l1 l2 : Level} {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  where

  is-prop-is-uniquely-eliminating-modality :
    is-prop (is-uniquely-eliminating-modality unit-○)
  is-prop-is-uniquely-eliminating-modality =
    is-prop-implicit-Π
      ( λ X →
        is-prop-Π
          ( λ P → is-property-is-local-dependent-type unit-○ (○ ∘ P)))

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
    ind-modality-is-uniquely-eliminating-modality is-uem-○ (λ _ → X) id

  is-section-unit-uniquely-eliminating-modality :
    (map-inv-unit-uniquely-eliminating-modality ∘ unit-○) ~ id
  is-section-unit-uniquely-eliminating-modality =
    compute-ind-modality-is-uniquely-eliminating-modality
      ( is-uem-○)
      ( λ _ → X)
      ( id)

  is-retraction-unit-uniquely-eliminating-modality :
    (unit-○ ∘ map-inv-unit-uniquely-eliminating-modality) ~ id
  is-retraction-unit-uniquely-eliminating-modality =
    htpy-eq
      ( ap pr1
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-uem-○ (λ _ → ○ X)) unit-○)
          ( unit-○ ∘ map-inv-unit-uniquely-eliminating-modality ,
            eq-htpy
              ( ap unit-○ ∘ (is-section-unit-uniquely-eliminating-modality)))
          ( id , refl)))

  is-modal-uniquely-eliminating-modality : is-modal unit-○ (○ X)
  is-modal-uniquely-eliminating-modality =
    is-equiv-is-invertible
      map-inv-unit-uniquely-eliminating-modality
      is-retraction-unit-uniquely-eliminating-modality
      is-section-unit-uniquely-eliminating-modality
```

### Uniquely eliminating modalities are uniquely determined by their modal types

Uniquely eliminating modalities are uniquely determined by their modal types.
Equivalently, this can be phrazed as a characterization of the identity type of
uniquely eliminating modalities.

Suppose given two uniquely eliminating modalities `○` and `●`. They are equal if
and only if they have the same modal types.

```agda
module _
  {l1 l2 : Level}
  where

  htpy-uniquely-eliminating-modality :
    (○ ● : uniquely-eliminating-modality l1 l2) → UU (lsuc l1 ⊔ l2)
  htpy-uniquely-eliminating-modality ○ ● =
    equiv-fam
      ( is-modal (unit-modality-uniquely-eliminating-modality ○))
      ( is-modal (unit-modality-uniquely-eliminating-modality ●))

  refl-htpy-uniquely-eliminating-modality :
    (○ : uniquely-eliminating-modality l1 l2) →
    htpy-uniquely-eliminating-modality ○ ○
  refl-htpy-uniquely-eliminating-modality ○ X = id-equiv

  htpy-eq-uniquely-eliminating-modality :
    (○ ● : uniquely-eliminating-modality l1 l2) →
    ○ ＝ ● → htpy-uniquely-eliminating-modality ○ ●
  htpy-eq-uniquely-eliminating-modality ○ .○ refl =
    refl-htpy-uniquely-eliminating-modality ○
```

It remains to show that `htpy-eq-uniquely-eliminating-modality` is an
equivalence.

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)

## References

{{#bibliography}} {{#reference RSS20}}
