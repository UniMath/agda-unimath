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

Given a family of commutative finite rings `A i` indexed by a finite type
`i : I`, their **dependent product** `Π(i:I), A i` is again a finite commutative
ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : 𝔽 l1) (A : type-𝔽 I → Commutative-Ring-𝔽 l2)
  where

  finite-ring-Π-Commutative-Ring-𝔽 : Ring-𝔽 (l1 ⊔ l2)
  finite-ring-Π-Commutative-Ring-𝔽 =
    Π-Ring-𝔽 I (λ i → finite-ring-Commutative-Ring-𝔽 (A i))

  ring-Π-Commutative-Ring-𝔽 : Ring (l1 ⊔ l2)
  ring-Π-Commutative-Ring-𝔽 =
    Π-Ring (type-𝔽 I) (ring-Commutative-Ring-𝔽 ∘ A)

  ab-Π-Commutative-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-Π-Commutative-Ring-𝔽 =
    ab-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  multiplicative-commutative-monoid-Π-Commutative-Ring-𝔽 :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-Π-Commutative-Ring-𝔽 =
    multiplicative-commutative-monoid-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  set-Π-Commutative-Ring-𝔽 : Set (l1 ⊔ l2)
  set-Π-Commutative-Ring-𝔽 =
    set-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  type-Π-Commutative-Ring-𝔽 : UU (l1 ⊔ l2)
  type-Π-Commutative-Ring-𝔽 =
    type-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  finite-type-Π-Commutative-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  finite-type-Π-Commutative-Ring-𝔽 =
    finite-type-Π-Ring-𝔽 I (finite-ring-Commutative-Ring-𝔽 ∘ A)

  is-finite-type-Π-Commutative-Ring-𝔽 : is-finite type-Π-Commutative-Ring-𝔽
  is-finite-type-Π-Commutative-Ring-𝔽 =
    is-finite-type-Π-Ring-𝔽 I (finite-ring-Commutative-Ring-𝔽 ∘ A)

  is-set-type-Π-Commutative-Ring-𝔽 : is-set type-Π-Commutative-Ring-𝔽
  is-set-type-Π-Commutative-Ring-𝔽 =
    is-set-type-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  add-Π-Commutative-Ring-𝔽 :
    type-Π-Commutative-Ring-𝔽 → type-Π-Commutative-Ring-𝔽 →
    type-Π-Commutative-Ring-𝔽
  add-Π-Commutative-Ring-𝔽 =
    add-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  zero-Π-Commutative-Ring-𝔽 : type-Π-Commutative-Ring-𝔽
  zero-Π-Commutative-Ring-𝔽 =
    zero-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  associative-add-Π-Commutative-Ring-𝔽 :
    (x y z : type-Π-Commutative-Ring-𝔽) →
    add-Π-Commutative-Ring-𝔽 (add-Π-Commutative-Ring-𝔽 x y) z ＝
    add-Π-Commutative-Ring-𝔽 x (add-Π-Commutative-Ring-𝔽 y z)
  associative-add-Π-Commutative-Ring-𝔽 =
    associative-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  left-unit-law-add-Π-Commutative-Ring-𝔽 :
    (x : type-Π-Commutative-Ring-𝔽) →
    add-Π-Commutative-Ring-𝔽 zero-Π-Commutative-Ring-𝔽 x ＝ x
  left-unit-law-add-Π-Commutative-Ring-𝔽 =
    left-unit-law-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  right-unit-law-add-Π-Commutative-Ring-𝔽 :
    (x : type-Π-Commutative-Ring-𝔽) →
    add-Π-Commutative-Ring-𝔽 x zero-Π-Commutative-Ring-𝔽 ＝ x
  right-unit-law-add-Π-Commutative-Ring-𝔽 =
    right-unit-law-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  commutative-add-Π-Commutative-Ring-𝔽 :
    (x y : type-Π-Commutative-Ring-𝔽) →
    add-Π-Commutative-Ring-𝔽 x y ＝ add-Π-Commutative-Ring-𝔽 y x
  commutative-add-Π-Commutative-Ring-𝔽 =
    commutative-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  mul-Π-Commutative-Ring-𝔽 :
    type-Π-Commutative-Ring-𝔽 → type-Π-Commutative-Ring-𝔽 →
    type-Π-Commutative-Ring-𝔽
  mul-Π-Commutative-Ring-𝔽 =
    mul-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  one-Π-Commutative-Ring-𝔽 : type-Π-Commutative-Ring-𝔽
  one-Π-Commutative-Ring-𝔽 =
    one-Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  associative-mul-Π-Commutative-Ring-𝔽 :
    (x y z : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 (mul-Π-Commutative-Ring-𝔽 x y) z ＝
    mul-Π-Commutative-Ring-𝔽 x (mul-Π-Commutative-Ring-𝔽 y z)
  associative-mul-Π-Commutative-Ring-𝔽 =
    associative-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  left-unit-law-mul-Π-Commutative-Ring-𝔽 :
    (x : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 one-Π-Commutative-Ring-𝔽 x ＝ x
  left-unit-law-mul-Π-Commutative-Ring-𝔽 =
    left-unit-law-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  right-unit-law-mul-Π-Commutative-Ring-𝔽 :
    (x : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 x one-Π-Commutative-Ring-𝔽 ＝ x
  right-unit-law-mul-Π-Commutative-Ring-𝔽 =
    right-unit-law-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  left-distributive-mul-add-Π-Commutative-Ring-𝔽 :
    (f g h : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 f (add-Π-Commutative-Ring-𝔽 g h) ＝
    add-Π-Commutative-Ring-𝔽
      ( mul-Π-Commutative-Ring-𝔽 f g)
      ( mul-Π-Commutative-Ring-𝔽 f h)
  left-distributive-mul-add-Π-Commutative-Ring-𝔽 =
    left-distributive-mul-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  right-distributive-mul-add-Π-Commutative-Ring-𝔽 :
    (f g h : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 (add-Π-Commutative-Ring-𝔽 f g) h ＝
    add-Π-Commutative-Ring-𝔽
      ( mul-Π-Commutative-Ring-𝔽 f h)
      ( mul-Π-Commutative-Ring-𝔽 g h)
  right-distributive-mul-add-Π-Commutative-Ring-𝔽 =
    right-distributive-mul-add-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  left-zero-law-mul-Π-Commutative-Ring-𝔽 :
    (f : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 zero-Π-Commutative-Ring-𝔽 f ＝
    zero-Π-Commutative-Ring-𝔽
  left-zero-law-mul-Π-Commutative-Ring-𝔽 =
    left-zero-law-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  right-zero-law-mul-Π-Commutative-Ring-𝔽 :
    (f : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 f zero-Π-Commutative-Ring-𝔽 ＝
    zero-Π-Commutative-Ring-𝔽
  right-zero-law-mul-Π-Commutative-Ring-𝔽 =
    right-zero-law-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  commutative-mul-Π-Commutative-Ring-𝔽 :
    (f g : type-Π-Commutative-Ring-𝔽) →
    mul-Π-Commutative-Ring-𝔽 f g ＝ mul-Π-Commutative-Ring-𝔽 g f
  commutative-mul-Π-Commutative-Ring-𝔽 =
    commutative-mul-Π-Commutative-Ring
      ( type-𝔽 I)
      ( commutative-ring-Commutative-Ring-𝔽 ∘ A)

  commutative-ring-Π-Commutative-Ring-𝔽 : Commutative-Ring (l1 ⊔ l2)
  commutative-ring-Π-Commutative-Ring-𝔽 =
    Π-Commutative-Ring (type-𝔽 I) (commutative-ring-Commutative-Ring-𝔽 ∘ A)

  Π-Commutative-Ring-𝔽 : Commutative-Ring-𝔽 (l1 ⊔ l2)
  pr1 Π-Commutative-Ring-𝔽 = finite-ring-Π-Commutative-Ring-𝔽
  pr2 Π-Commutative-Ring-𝔽 = commutative-mul-Π-Commutative-Ring-𝔽
```
