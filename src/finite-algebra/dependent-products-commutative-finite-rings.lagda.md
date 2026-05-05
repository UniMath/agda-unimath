# Dependent products of commutative finit rings

```agda
module finite-algebra.dependent-products-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-commutative-rings

open import finite-algebra.commutative-finite-rings
open import finite-algebra.dependent-products-finite-rings
open import finite-algebra.finite-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids

open import ring-theory.dependent-products-rings
open import ring-theory.rings

open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given a family of
[commutative finite rings](finite-algebra.commutative-finite-rings.md) `A i`
indexed by a [finite type](univalent-combinatorics.finite-types.md) `i : I`,
their
{{#concept "dependent product" Disambiguation="of finite family of commutative finite rings" Agda=Π-Finite-Commutative-Ring}}
`Π(i:I), A i` is again a finite commutative ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : Finite-Type l1)
  (A : type-Finite-Type I → Finite-Commutative-Ring l2)
  where

  finite-ring-Π-Finite-Commutative-Ring : Finite-Ring (l1 ⊔ l2)
  finite-ring-Π-Finite-Commutative-Ring =
    Π-Finite-Ring I (λ i → finite-ring-Finite-Commutative-Ring (A i))

  ring-Π-Finite-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-Π-Finite-Commutative-Ring =
    Π-Ring (type-Finite-Type I) (ring-Finite-Commutative-Ring ∘ A)

  ab-Π-Finite-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-Π-Finite-Commutative-Ring =
    ab-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  multiplicative-commutative-monoid-Π-Finite-Commutative-Ring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-Π-Finite-Commutative-Ring =
    multiplicative-commutative-monoid-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  set-Π-Finite-Commutative-Ring : Set (l1 ⊔ l2)
  set-Π-Finite-Commutative-Ring =
    set-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  type-Π-Finite-Commutative-Ring : UU (l1 ⊔ l2)
  type-Π-Finite-Commutative-Ring =
    type-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  finite-type-Π-Finite-Commutative-Ring : Finite-Type (l1 ⊔ l2)
  finite-type-Π-Finite-Commutative-Ring =
    finite-type-Π-Finite-Ring I (finite-ring-Finite-Commutative-Ring ∘ A)

  is-finite-type-Π-Finite-Commutative-Ring :
    is-finite type-Π-Finite-Commutative-Ring
  is-finite-type-Π-Finite-Commutative-Ring =
    is-finite-type-Π-Finite-Ring I (finite-ring-Finite-Commutative-Ring ∘ A)

  is-set-type-Π-Finite-Commutative-Ring : is-set type-Π-Finite-Commutative-Ring
  is-set-type-Π-Finite-Commutative-Ring =
    is-set-type-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  add-Π-Finite-Commutative-Ring :
    type-Π-Finite-Commutative-Ring → type-Π-Finite-Commutative-Ring →
    type-Π-Finite-Commutative-Ring
  add-Π-Finite-Commutative-Ring =
    add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  zero-Π-Finite-Commutative-Ring : type-Π-Finite-Commutative-Ring
  zero-Π-Finite-Commutative-Ring =
    zero-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  associative-add-Π-Finite-Commutative-Ring :
    (x y z : type-Π-Finite-Commutative-Ring) →
    add-Π-Finite-Commutative-Ring (add-Π-Finite-Commutative-Ring x y) z ＝
    add-Π-Finite-Commutative-Ring x (add-Π-Finite-Commutative-Ring y z)
  associative-add-Π-Finite-Commutative-Ring =
    associative-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  left-unit-law-add-Π-Finite-Commutative-Ring :
    (x : type-Π-Finite-Commutative-Ring) →
    add-Π-Finite-Commutative-Ring zero-Π-Finite-Commutative-Ring x ＝ x
  left-unit-law-add-Π-Finite-Commutative-Ring =
    left-unit-law-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  right-unit-law-add-Π-Finite-Commutative-Ring :
    (x : type-Π-Finite-Commutative-Ring) →
    add-Π-Finite-Commutative-Ring x zero-Π-Finite-Commutative-Ring ＝ x
  right-unit-law-add-Π-Finite-Commutative-Ring =
    right-unit-law-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  commutative-add-Π-Finite-Commutative-Ring :
    (x y : type-Π-Finite-Commutative-Ring) →
    add-Π-Finite-Commutative-Ring x y ＝ add-Π-Finite-Commutative-Ring y x
  commutative-add-Π-Finite-Commutative-Ring =
    commutative-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  mul-Π-Finite-Commutative-Ring :
    type-Π-Finite-Commutative-Ring → type-Π-Finite-Commutative-Ring →
    type-Π-Finite-Commutative-Ring
  mul-Π-Finite-Commutative-Ring =
    mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  one-Π-Finite-Commutative-Ring : type-Π-Finite-Commutative-Ring
  one-Π-Finite-Commutative-Ring =
    one-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  associative-mul-Π-Finite-Commutative-Ring :
    (x y z : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring (mul-Π-Finite-Commutative-Ring x y) z ＝
    mul-Π-Finite-Commutative-Ring x (mul-Π-Finite-Commutative-Ring y z)
  associative-mul-Π-Finite-Commutative-Ring =
    associative-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  left-unit-law-mul-Π-Finite-Commutative-Ring :
    (x : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring one-Π-Finite-Commutative-Ring x ＝ x
  left-unit-law-mul-Π-Finite-Commutative-Ring =
    left-unit-law-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  right-unit-law-mul-Π-Finite-Commutative-Ring :
    (x : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring x one-Π-Finite-Commutative-Ring ＝ x
  right-unit-law-mul-Π-Finite-Commutative-Ring =
    right-unit-law-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  left-distributive-mul-add-Π-Finite-Commutative-Ring :
    (f g h : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring f (add-Π-Finite-Commutative-Ring g h) ＝
    add-Π-Finite-Commutative-Ring
      ( mul-Π-Finite-Commutative-Ring f g)
      ( mul-Π-Finite-Commutative-Ring f h)
  left-distributive-mul-add-Π-Finite-Commutative-Ring =
    left-distributive-mul-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  right-distributive-mul-add-Π-Finite-Commutative-Ring :
    (f g h : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring (add-Π-Finite-Commutative-Ring f g) h ＝
    add-Π-Finite-Commutative-Ring
      ( mul-Π-Finite-Commutative-Ring f h)
      ( mul-Π-Finite-Commutative-Ring g h)
  right-distributive-mul-add-Π-Finite-Commutative-Ring =
    right-distributive-mul-add-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  left-zero-law-mul-Π-Finite-Commutative-Ring :
    (f : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring zero-Π-Finite-Commutative-Ring f ＝
    zero-Π-Finite-Commutative-Ring
  left-zero-law-mul-Π-Finite-Commutative-Ring =
    left-zero-law-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  right-zero-law-mul-Π-Finite-Commutative-Ring :
    (f : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring f zero-Π-Finite-Commutative-Ring ＝
    zero-Π-Finite-Commutative-Ring
  right-zero-law-mul-Π-Finite-Commutative-Ring =
    right-zero-law-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  commutative-mul-Π-Finite-Commutative-Ring :
    (f g : type-Π-Finite-Commutative-Ring) →
    mul-Π-Finite-Commutative-Ring f g ＝ mul-Π-Finite-Commutative-Ring g f
  commutative-mul-Π-Finite-Commutative-Ring =
    commutative-mul-Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  commutative-ring-Π-Finite-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  commutative-ring-Π-Finite-Commutative-Ring =
    Π-Commutative-Ring
      ( type-Finite-Type I)
      ( commutative-ring-Finite-Commutative-Ring ∘ A)

  Π-Finite-Commutative-Ring : Finite-Commutative-Ring (l1 ⊔ l2)
  pr1 Π-Finite-Commutative-Ring = finite-ring-Π-Finite-Commutative-Ring
  pr2 Π-Finite-Commutative-Ring = commutative-mul-Π-Finite-Commutative-Ring
```
