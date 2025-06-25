# Noncontractible types

```agda
module foundation.noncontractible-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

_Noncontractibility_ is a positive way of stating that a type is
[not](foundation.negation.md)
[contractible](foundation-core.contractible-types.md). A type `A` is
{{#concept "noncontractible" Agda=is-noncontractible}} if it is
[empty](foundation.empty-types.md), or, inductively, if there
[exists](foundation.existential-quantification.md) two elements `x y : A` whose
[identity type](foundation-core.identity-types.md) `x ＝ y` is noncontractible.
More specifically, we may say `A` has an
$n$-{{#concept "noncontractibility" Agda=noncontractibility'}} if there are
$n$-identifications `p` and `q` in `A` such that `p ≠ q`. When a type is
noncontractible in this sense, it is [apart](foundation.apartness-relations.md)
from the [unit type](foundation.unit-type.md).

## Definitions

### The negation of being contractible

```agda
is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)
```

### Noncontractibilities of a type

```agda
noncontractibility' : {l : Level} → UU l → ℕ → UU l
noncontractibility' A zero-ℕ = is-empty A
noncontractibility' A (succ-ℕ k) =
  Σ A (λ x → Σ A (λ y → noncontractibility' (x ＝ y) k))

noncontractibility : {l : Level} → UU l → UU l
noncontractibility A = Σ ℕ (noncontractibility' A)
```

### The property of being noncontractible

```agda
is-noncontractible' : {l : Level} → UU l → ℕ → UU l
is-noncontractible' A zero-ℕ = is-empty A
is-noncontractible' A (succ-ℕ n) =
  is-inhabited (noncontractibility' A (succ-ℕ n))

is-prop-is-noncontractible' :
  {l : Level} {A : UU l} {n : ℕ} → is-prop (is-noncontractible' A n)
is-prop-is-noncontractible' {n = zero-ℕ} = is-property-is-empty
is-prop-is-noncontractible' {n = succ-ℕ n} = is-property-is-inhabited _
```

```agda
is-noncontractible : {l : Level} → UU l → UU l
is-noncontractible A = is-inhabited (noncontractibility A)
```

## Properties

### Empty types are not contractible

```agda
is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id

noncontractibility-is-empty :
  {l : Level} {X : UU l} → is-empty X → noncontractibility X
noncontractibility-is-empty H = 0 , H

noncontractibility-empty : noncontractibility empty
noncontractibility-empty = 0 , id
```

### Noncontractible types are not contractible

```agda
is-not-contractible-noncontractibility :
  {l : Level} {X : UU l} → noncontractibility X → is-not-contractible X
is-not-contractible-noncontractibility (zero-ℕ , H) =
  is-not-contractible-is-empty H
is-not-contractible-noncontractibility (succ-ℕ n , x , y , H) C =
  is-not-contractible-noncontractibility (n , H) (is-prop-is-contr C x y)
```

## Comments

The dimension of noncontractibility of a type is not unique. For instance,
consider the disjoint sum of the unit type and the
[circle](synthetic-homotopy-theory.circle.md) `1 + 𝕊¹`. This type has a
1-noncontractibility as the two base points are not equal, but it also has a
2-noncontractiblity between the reflexivity at the basepoint of the circle and
the free loop. In fact, the free fixed point of the operation `1 + Σ(-)`, where
`Σ` is the
[suspension operator](synthetic-homotopy-theory.suspensions-of-types.md), is
$n$-noncontractible for every $n ≥ 1$.

## See also

- [Noninjective maps](foundation.noninjective-maps.md)
