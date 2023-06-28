# The open modalities

```agda
module orthogonal-factorization-systems.open-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.propositions
open import foundation.transport
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given any proposition `Q`, the hom functor `Q →_` defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md). We
call these the **open modalities**.

## Definition

```agda
operator-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) → operator-modality l (lQ ⊔ l)
operator-open-modality l Q X = type-Prop Q → X

locally-small-operator-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) →
  locally-small-operator-modality l (lQ ⊔ l) (lQ ⊔ l)
pr1 (locally-small-operator-open-modality l Q) = operator-open-modality l Q
pr2 (locally-small-operator-open-modality l Q) X = is-locally-small'

unit-open-modality :
  {l lQ : Level} (Q : Prop lQ) → unit-modality (operator-open-modality l Q)
unit-open-modality Q x _ = x
```

## Properties

### The open modalities are higher modalities

```agda
module _
  {l lQ : Level} (Q : Prop lQ)
  where

  ind-open-modality : ind-modality {l} (unit-open-modality Q)
  ind-open-modality X P f z q =
    tr P (eq-htpy λ q' → ap z (eq-is-prop (is-prop-type-Prop Q))) (f (z q) q)

  compute-ind-open-modality :
    compute-ind-modality {l} (unit-open-modality Q) (ind-open-modality)
  compute-ind-open-modality X P f a =
    eq-htpy
    ( λ q →
      ap
        ( λ p → tr P p (f a q))
        ( ( ap
            ( eq-htpy)
            ( eq-htpy
              ( λ _ → ap-const a (eq-is-prop (is-prop-type-Prop Q))))) ∙
          ( eq-htpy-refl-htpy (λ _ → a))))

  dependent-universal-property-open-modality :
    dependent-universal-property-modality {l} (unit-open-modality Q)
  pr1 dependent-universal-property-open-modality = ind-open-modality
  pr2 dependent-universal-property-open-modality = compute-ind-open-modality
```

For local smallness with respect to the appropriate universe level, we must take
the maximum of `l` and `lQ` as our domain. In practice, this allows `lQ` to be
smaller than `l`.

```agda
module _
  (l : Level) {lQ : Level} (Q : Prop lQ)
  where

  is-modal-identity-types-open-modality :
    is-modal-identity-types
      ( locally-small-operator-open-modality (l ⊔ lQ) Q)
      ( unit-open-modality Q)
  is-modal-identity-types-open-modality X x y =
    is-equiv-has-inverse
      ( λ z → eq-htpy (λ q → htpy-eq (z q) q))
      ( λ z →
        eq-htpy
          ( λ q →
            ( ap
              ( eq-htpy)
              ( eq-htpy
                ( λ q' →
                  ap
                    ( λ q'' → htpy-eq (z q'') q')
                    ( eq-is-prop (is-prop-type-Prop Q))))) ∙
            ( is-retraction-eq-htpy (z q))))
      ( is-retraction-eq-htpy)

  is-higher-modality-open-modality :
    is-higher-modality
      ( locally-small-operator-open-modality (l ⊔ lQ) Q)
      ( unit-open-modality Q)
  pr1 is-higher-modality-open-modality =
    dependent-universal-property-open-modality Q
  pr2 is-higher-modality-open-modality =
    is-modal-identity-types-open-modality

  open-higher-modality : higher-modality (l ⊔ lQ) (l ⊔ lQ)
  pr1 open-higher-modality = locally-small-operator-open-modality (l ⊔ lQ) Q
  pr1 (pr2 open-higher-modality) = unit-open-modality Q
  pr2 (pr2 open-higher-modality) = is-higher-modality-open-modality
```

### The open modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) →
  is-uniquely-eliminating-modality {l ⊔ lQ} (unit-open-modality Q)
is-uniquely-eliminating-modality-open-modality l Q =
  is-uniquely-eliminating-modality-higher-modality (open-higher-modality l Q)
```
