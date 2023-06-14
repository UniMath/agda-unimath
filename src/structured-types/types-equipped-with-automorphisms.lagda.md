# Types equipped with automorphisms

```agda
module structured-types.types-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels
```

</details>

## Idea

A type equipped with an automorphism is a pair consisting of a type `A` and an
automorphism on `A`.

## Definition

```agda
Type-Aut : (l : Level) → UU (lsuc l)
Type-Aut l = Σ (UU l) (Aut)

type-Type-Aut : {l : Level} → Type-Aut l → UU l
type-Type-Aut (X , e) = X

aut-Type-Aut : {l : Level} (A : Type-Aut l) → Aut (type-Type-Aut A)
aut-Type-Aut (X , e) = e
```

## Properties

### Every type can be equipped with the identity automorpism

```agda
id-Type-Aut : {l : Level} → UU l → Type-Aut l
pr1 (id-Type-Aut X) = X
pr2 (id-Type-Aut X) = id-equiv
```
