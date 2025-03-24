# Reflective modalities

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems.reflective-modalities
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators funext univalence truncations
open import orthogonal-factorization-systems.reflective-subuniverses funext univalence truncations
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

- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)
