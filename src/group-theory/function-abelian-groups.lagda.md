# Function groups of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.function-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types funext
open import foundation.sets funext
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.dependent-products-abelian-groups funext
open import group-theory.groups funext
open import group-theory.monoids funext
open import group-theory.semigroups funext
```

</details>

## Idea

Given an abelian group `G` and a type `X`, the function group `G^X` consists of
functions from `X` to the underlying type of `G`. The group operations are given
pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (X : UU l2)
  where

  function-Ab : Ab (l1 ⊔ l2)
  function-Ab = Π-Ab X (λ _ → A)

  group-function-Ab : Group (l1 ⊔ l2)
  group-function-Ab = group-Π-Ab X (λ _ → A)

  semigroup-function-Ab : Semigroup (l1 ⊔ l2)
  semigroup-function-Ab = semigroup-Π-Ab X (λ _ → A)

  set-function-Ab : Set (l1 ⊔ l2)
  set-function-Ab = set-Π-Ab X (λ _ → A)

  type-function-Ab : UU (l1 ⊔ l2)
  type-function-Ab = type-Π-Ab X (λ _ → A)

  add-function-Ab :
    (f g : type-function-Ab) → type-function-Ab
  add-function-Ab = add-Π-Ab X (λ _ → A)

  associative-add-function-Ab :
    (f g h : type-function-Ab) →
    add-function-Ab (add-function-Ab f g) h ＝
    add-function-Ab f (add-function-Ab g h)
  associative-add-function-Ab = associative-add-Π-Ab X (λ _ → A)

  zero-function-Ab : type-function-Ab
  zero-function-Ab = zero-Π-Ab X (λ _ → A)

  left-unit-law-add-function-Ab :
    (f : type-function-Ab) → add-function-Ab zero-function-Ab f ＝ f
  left-unit-law-add-function-Ab = left-unit-law-add-Π-Ab X (λ _ → A)

  right-unit-law-add-function-Ab :
    (f : type-function-Ab) → add-function-Ab f zero-function-Ab ＝ f
  right-unit-law-add-function-Ab = right-unit-law-add-Π-Ab X (λ _ → A)

  monoid-function-Ab : Monoid (l1 ⊔ l2)
  monoid-function-Ab = monoid-Π-Ab X (λ _ → A)

  neg-function-Ab : type-function-Ab → type-function-Ab
  neg-function-Ab = neg-Π-Ab X (λ _ → A)

  left-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab (neg-function-Ab f) f ＝ zero-function-Ab
  left-inverse-law-add-function-Ab =
    left-inverse-law-add-Π-Ab X (λ _ → A)

  right-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab f (neg-function-Ab f) ＝ zero-function-Ab
  right-inverse-law-add-function-Ab =
    right-inverse-law-add-Π-Ab X (λ _ → A)

  commutative-add-function-Ab :
    (f g : type-function-Ab) →
    add-function-Ab f g ＝ add-function-Ab g f
  commutative-add-function-Ab = commutative-add-Π-Ab X (λ _ → A)
```
