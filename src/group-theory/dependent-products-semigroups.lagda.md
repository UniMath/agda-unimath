# Dependent products of semigroups

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.dependent-products-semigroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.semigroups funext univalence
```

</details>

## Idea

Given a family of semigroups `Gᵢ` indexed by `i : I`, the dependent product
`Π(i : I), Gᵢ` is the semigroup consisting of dependent functions assigning to
each `i : I` an element of the underlying type of `Gᵢ`. The semigroup operation
is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (G : I → Semigroup l2)
  where

  set-Π-Semigroup : Set (l1 ⊔ l2)
  set-Π-Semigroup = Π-Set' I (λ i → set-Semigroup (G i))

  type-Π-Semigroup : UU (l1 ⊔ l2)
  type-Π-Semigroup = type-Set set-Π-Semigroup

  mul-Π-Semigroup :
    (f g : type-Π-Semigroup) → type-Π-Semigroup
  mul-Π-Semigroup f g i = mul-Semigroup (G i) (f i) (g i)

  associative-mul-Π-Semigroup :
    (f g h : type-Π-Semigroup) →
    mul-Π-Semigroup (mul-Π-Semigroup f g) h ＝
    mul-Π-Semigroup f (mul-Π-Semigroup g h)
  associative-mul-Π-Semigroup f g h =
    eq-htpy (λ i → associative-mul-Semigroup (G i) (f i) (g i) (h i))

  has-associative-mul-Π-Semigroup :
    has-associative-mul-Set set-Π-Semigroup
  pr1 has-associative-mul-Π-Semigroup =
    mul-Π-Semigroup
  pr2 has-associative-mul-Π-Semigroup =
    associative-mul-Π-Semigroup

  Π-Semigroup : Semigroup (l1 ⊔ l2)
  pr1 Π-Semigroup = set-Π-Semigroup
  pr2 Π-Semigroup = has-associative-mul-Π-Semigroup
```
