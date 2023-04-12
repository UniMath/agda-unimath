# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A **reflective subuniverse** is a subuniverse `P` together with a modal operator
`○` such that `○ A` is in `P` for all small types `A`, and a modal unit with the
property that the types in `P` are local at the modal unit for all small types
`A`. Hence the modal types with respect to `○` are precisely the types in the
reflective subuniverse.

## Definition

```agda
module _
  {l lM : Level} {○ : modal-operator l l} (unit-○ : modal-unit ○)
  (is-modal' : UU l → Prop lM)
  where

  is-reflective-subuniverse : UU (lsuc l ⊔ lM)
  is-reflective-subuniverse =
    ( (X : UU l) → type-Prop (is-modal' (○ X))) ×
    ( (X : UU l) → type-Prop (is-modal' X) →
      (Y : UU l) → is-local-type (unit-○ {Y}) X)

reflective-subuniverse : (l lM : Level) → UU (lsuc l ⊔ lsuc lM)
reflective-subuniverse l lM =
  Σ ( modal-operator l l)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( λ unit-○ →
          Σ ( UU l → Prop lM)
            ( is-reflective-subuniverse unit-○)))
```

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
