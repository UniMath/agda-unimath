# Σ-closed subuniverses

```agda
module foundation.sigma-closed-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels
```

</details>

## Idea

A [subuniverse](foundation.subuniverses.md) `P` is **Σ-closed** if it is closed
under the formation of [Σ-types](foundation.dependent-pair-types.md). Meaning
`P` is Σ-closed if `Σ A B` is in `P` whenever `B` is a family of types in `P`
over a type `A` in `P`.

## Definition

```agda
is-Σ-closed-subuniverse :
  {l lP : Level} → subuniverse l lP → UU (lsuc l ⊔ lP)
is-Σ-closed-subuniverse {l} P =
  (A : UU l) → type-Prop (P A) →
  (B : A → UU l) → ((x : A) → type-Prop (P (B x))) →
  type-Prop (P (Σ A B))

Σ-closed-subuniverse :
  (l lP : Level) → UU (lsuc l ⊔ lsuc lP)
Σ-closed-subuniverse l lP =
  Σ ( subuniverse l lP)
    ( is-Σ-closed-subuniverse)
```

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
