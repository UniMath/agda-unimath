# Families of types over telescopes

```agda
module foundation.families-over-telescopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.telescopes
open import foundation.universe-levels

open import foundation-core.raising-universe-levels
```

</details>

## Idea

A
{{#concept "type family" Disambiguation="over a telescope" Agda=family-over-telescope}}
over a [telescope](foundation.telescopes.md) is a family of types defined in the
context of the telescope.

For instance, given a length three telescope

```text
  Γ := ⟨x : A, y : B x, z : C x y z⟩
```

a type family over `Γ` is a ternary family of types

```text
  D : (x : A) (y : B x) (z : C x y z) → 𝒰.
```

## Definitions

### Type families over telescopes

```agda
family-over-telescope :
  {l1 : Level} (l2 : Level) {n : ℕ} → telescope l1 n → UU (l1 ⊔ lsuc l2)
family-over-telescope {l1} l2 (base-telescope X) =
  raise (l1 ⊔ lsuc l2) (UU l2)
family-over-telescope l2 (cons-telescope {X = X} Γ) =
  (x : X) → family-over-telescope l2 (Γ x)
```
