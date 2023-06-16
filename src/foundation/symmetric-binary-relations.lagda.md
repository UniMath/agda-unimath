# Symmetric binary relations

```agda
module foundation.symmetric-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-type-families
open import foundation.equivalences
open import foundation.transport
open import foundation.universe-levels
open import foundation.unordered-pairs
```

</details>

## Idea

A **symmetric binary relation** on a type `A` is a type family `R` over the type
of [unordered pairs](foundation.unordered-pairs.md) of elements of `A`. Given a
symmetric binary relation `R` on `A` and an equivalence of unordered pairs
`p ＝ q`, we have `R p ≃ R q`. In particular, we have

```text
  R ({x,y}) ≃ R ({y,x})
```

for any two elements `x y : A`, where `{x,y}` is the _standard unordered pair_
consisting of `x` and `y`.

## Definitions

### Symmetric binary relations

```agda
symmetric-binary-relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
symmetric-binary-relation l2 A = unordered-pair A → UU l2
```

### Symmetries of symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : symmetric-binary-relation l2 A)
  where

  equiv-tr-symmetric-binary-relation :
    (p q : unordered-pair A) → Eq-unordered-pair p q → R p ≃ R q
  equiv-tr-symmetric-binary-relation p q e =
    equiv-tr R (eq-Eq-unordered-pair' p q e)

  tr-symmetric-binary-relation :
    (p q : unordered-pair A) → Eq-unordered-pair p q → R p → R q
  tr-symmetric-binary-relation p q e =
    map-equiv (equiv-tr-symmetric-binary-relation p q e)
```
