# Function semigroups

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.function-semigroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.dependent-products-semigroups funext univalence
open import group-theory.semigroups funext univalence
```

</details>

## Idea

Given a semigroup `G` and a type `X`, the function semigroup `G^X` consists of
functions from `X` to the underlying type of `G`. The semigroup operation is
given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (X : UU l2)
  where

  function-Semigroup : Semigroup (l1 ⊔ l2)
  function-Semigroup = Π-Semigroup X (λ _ → G)

  set-function-Semigroup : Set (l1 ⊔ l2)
  set-function-Semigroup = set-Π-Semigroup X (λ _ → G)

  type-function-Semigroup : UU (l1 ⊔ l2)
  type-function-Semigroup = type-Π-Semigroup X (λ _ → G)

  mul-function-Semigroup :
    (f g : type-function-Semigroup) → type-function-Semigroup
  mul-function-Semigroup = mul-Π-Semigroup X (λ _ → G)

  associative-mul-function-Semigroup :
    (f g h : type-function-Semigroup) →
    mul-function-Semigroup (mul-function-Semigroup f g) h ＝
    mul-function-Semigroup f (mul-function-Semigroup g h)
  associative-mul-function-Semigroup =
    associative-mul-Π-Semigroup X (λ _ → G)

  has-associative-mul-function-Semigroup :
    has-associative-mul-Set set-function-Semigroup
  has-associative-mul-function-Semigroup =
    has-associative-mul-Π-Semigroup X (λ _ → G)
```
