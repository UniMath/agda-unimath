# Σ-closed reflective subuniverses

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.sigma-closed-reflective-subuniverses
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sigma-closed-subuniverses funext
open import foundation.universe-levels

open import orthogonal-factorization-systems.reflective-subuniverses funext
```

</details>

## Idea

A
[reflective subuniverse](orthogonal-factorization-systems.reflective-subuniverses.md)
is **Σ-closed** if it is closed under the formation of
[Σ-types](foundation.dependent-pair-types.md).

## Definition

```agda
is-closed-under-Σ-reflective-subuniverse :
  {l lP : Level} → reflective-subuniverse l lP → UU (lsuc l ⊔ lP)
is-closed-under-Σ-reflective-subuniverse (P , _) =
  is-closed-under-Σ-subuniverse P

closed-under-Σ-reflective-subuniverse :
  (l lP : Level) → UU (lsuc l ⊔ lsuc lP)
closed-under-Σ-reflective-subuniverse l lP =
  Σ ( reflective-subuniverse l lP)
    ( is-closed-under-Σ-reflective-subuniverse)
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)

## References

{{#bibliography}} {{#reference RSS20}}
