# Trivial commutative rings

```agda
module commutative-algebra.trivial-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.isomorphisms-commutative-rings

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import group-theory.abelian-groups
open import group-theory.trivial-groups

open import ring-theory.rings
open import ring-theory.trivial-rings
```

</details>

## Idea

**Trivial commutative rings** are commutative rings in which `0 = 1`.

## Definition

```agda
is-trivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-trivial-commutative-ring-Prop A =
  Id-Prop
    ( set-Commutative-Ring A)
    ( zero-Commutative-Ring A)
    ( one-Commutative-Ring A)

is-trivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-trivial-Commutative-Ring A =
  type-Prop (is-trivial-commutative-ring-Prop A)

is-prop-is-trivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-prop (is-trivial-Commutative-Ring A)
is-prop-is-trivial-Commutative-Ring A =
  is-prop-type-Prop (is-trivial-commutative-ring-Prop A)

is-nontrivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-nontrivial-commutative-ring-Prop A =
  neg-Prop (is-trivial-commutative-ring-Prop A)

is-nontrivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-nontrivial-Commutative-Ring A =
  type-Prop (is-nontrivial-commutative-ring-Prop A)

is-prop-is-nontrivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-prop (is-nontrivial-Commutative-Ring A)
is-prop-is-nontrivial-Commutative-Ring A =
  is-prop-type-Prop (is-nontrivial-commutative-ring-Prop A)
```

## Properties

### The carrier type of a zero commutative ring is contractible

```agda
is-contr-is-trivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-trivial-Commutative-Ring A →
  is-contr (type-Commutative-Ring A)
is-contr-is-trivial-Commutative-Ring A p =
  is-contr-is-trivial-Ring (ring-Commutative-Ring A) p
```

### The trivial ring

```agda
trivial-Ring : Ring lzero
pr1 trivial-Ring = trivial-Ab
pr1 (pr1 (pr2 trivial-Ring)) x y = star
pr2 (pr1 (pr2 trivial-Ring)) x y z = refl
pr1 (pr1 (pr2 (pr2 trivial-Ring))) = star
pr1 (pr2 (pr1 (pr2 (pr2 trivial-Ring)))) star = refl
pr2 (pr2 (pr1 (pr2 (pr2 trivial-Ring)))) star = refl
pr2 (pr2 (pr2 trivial-Ring)) = (λ a b c → refl) , (λ a b c → refl)

is-commutative-trivial-Ring : is-commutative-Ring trivial-Ring
is-commutative-trivial-Ring x y = refl

trivial-Commutative-Ring : Commutative-Ring lzero
trivial-Commutative-Ring = (trivial-Ring , is-commutative-trivial-Ring)

is-trivial-trivial-Commutative-Ring :
  is-trivial-Commutative-Ring trivial-Commutative-Ring
is-trivial-trivial-Commutative-Ring = refl
```

### The zero of a commutative ring is invertible if and only if the commutative ring is trivial

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    is-invertible-zero-is-trivial-Commutative-Ring :
      is-trivial-Commutative-Ring R →
      is-invertible-element-Commutative-Ring R (zero-Commutative-Ring R)
    is-invertible-zero-is-trivial-Commutative-Ring 0=1 =
      ( one-Commutative-Ring R ,
        ( ( ap-mul-Commutative-Ring R 0=1 refl) ∙
          ( right-unit-law-mul-Commutative-Ring R _)) ,
        ( ( ap-mul-Commutative-Ring R refl 0=1) ∙
          ( left-unit-law-mul-Commutative-Ring R _)))

    is-trivial-is-invertible-zero-Commutative-Ring :
      is-invertible-element-Commutative-Ring R (zero-Commutative-Ring R) →
      is-trivial-Commutative-Ring R
    is-trivial-is-invertible-zero-Commutative-Ring (r , 0r=1 , _) =
      inv (left-zero-law-mul-Commutative-Ring R r) ∙ 0r=1
```

### The type of trivial rings is contractible

To-do: complete proof of uniqueness of the zero ring using SIP, ideally refactor
code to do zero algebras all along the chain to prettify and streamline future
work
