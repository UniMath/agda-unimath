# Models

```agda
module universal-algebra.models-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.signatures
```

</details>

## Idea

A model of a signature `Sig` in a type `A` is a dependent function that assings
to each function symbol `f` of arity `n` and a vector of `n` elements of `A` an
element of `A`.

## Definitions

### Models

```agda
module _ {l1 : Level} (Sig : signature l1) where

  is-model : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model X =
    ( f : operations-signature Sig) →
    ( vec X (arity-operations-signature Sig f) → X)

  is-model-Set : {l2 : Level} → (Set l2) → UU (l1 ⊔ l2)
  is-model-Set X = is-model (type-Set X)

  Model : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model l2 = Σ (Set l2) (λ X → is-model-Set X)

  set-Model : {l2 : Level} → Model l2 → Set l2
  set-Model M = pr1 M

  is-model-set-Model :
    { l2 : Level} →
    ( M : Model l2) →
    is-model-Set (set-Model M)
  is-model-set-Model M = pr2 M

  type-Model : {l2 : Level} → Model l2 → UU l2
  type-Model M = pr1 (set-Model M)

  is-set-type-Model :
    { l2 : Level} →
    ( M : Model l2) →
    is-set (type-Model M)
  is-set-type-Model M = pr2 (set-Model M)
```
