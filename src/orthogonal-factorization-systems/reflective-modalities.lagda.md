# Reflective modalities

```agda
module orthogonal-factorization-systems.reflective-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-subuniverses
```

</details>

## Idea

A [modal operator](orthogonal-factorization-systems.modal-operators.md) with
unit is **reflective** if its [subuniverse](foundation.subuniverses.md) of modal
types is
[reflective](orthogonal-factorization-systems.reflective-subuniverses.md).

## Definitions

### Reflective subuniverses

```agda
is-reflective-modality :
  {l : Level} {○ : operator-modality l l} → unit-modality ○ → UU (lsuc l)
is-reflective-modality unit-○ =
  is-reflective-subuniverse (modal-type-subuniverse unit-○)

reflective-modality : (l : Level) → UU (lsuc l)
reflective-modality l =
  Σ (operator-modality l l) (λ ○ → Σ (unit-modality ○) (is-reflective-modality))
```

## See also

- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
