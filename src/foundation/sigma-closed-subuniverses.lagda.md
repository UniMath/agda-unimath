# Σ-closed subuniverses

```agda
module foundation.sigma-closed-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

A [subuniverse](foundation.subuniverses.md) `P` is **Σ-closed** if it is closed
under the formation of [Σ-types](foundation.dependent-pair-types.md). Meaning
`P` is Σ-closed if `Σ A B` is in `P` whenever `B` is a family of types in `P`
over a type `A` in `P`.

## Definition

We state a general form involving three universes, and a more traditional form
using a single universe

```agda
is-closed-under-Σ-subuniverses :
  {l1 l2 lP lQ lR : Level}
  (P : subuniverse l1 lP)
  (Q : subuniverse l2 lQ)
  (R : subuniverse (l1 ⊔ l2) lR) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ lP ⊔ lQ ⊔ lR)
is-closed-under-Σ-subuniverses P Q R =
  (X : type-subuniverse P)
  (Y : inclusion-subuniverse P X → type-subuniverse Q) →
  is-in-subuniverse R
    ( Σ (inclusion-subuniverse P X) (inclusion-subuniverse Q ∘ Y))

is-closed-under-Σ-subuniverse :
  {l lP : Level} → subuniverse l lP → UU (lsuc l ⊔ lP)
is-closed-under-Σ-subuniverse P = is-closed-under-Σ-subuniverses P P P

closed-under-Σ-subuniverse :
  (l lP : Level) → UU (lsuc l ⊔ lsuc lP)
closed-under-Σ-subuniverse l lP =
  Σ (subuniverse l lP) (is-closed-under-Σ-subuniverse)
```

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
