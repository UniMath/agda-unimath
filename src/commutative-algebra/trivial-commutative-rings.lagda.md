# Trivial commutative rings

```agda
module commutative-algebra.trivial-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
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

### The type of zero commutative rings is contractible

```agda
0-ring : Ring lzero
pr1 0-ring = ab-0-group
pr1 (pr1 (pr2 0-ring)) = λ x y → star
pr2 (pr1 (pr2 0-ring)) = λ x y z → refl
pr1 (pr1 (pr2 (pr2 0-ring))) = star
pr1 (pr2 (pr1 (pr2 (pr2 0-ring)))) star = refl
pr2 (pr2 (pr1 (pr2 (pr2 0-ring)))) star = refl
pr2 (pr2 (pr2 0-ring)) = (λ a b c → refl) , (λ a b c → refl)

is-commutative-0-Ring : is-commutative-Ring 0-ring
is-commutative-0-Ring = λ x y → refl

0-cRing : Commutative-Ring lzero
0-cRing = 0-ring , is-commutative-0-Ring

is-trivial-0-cRing : is-trivial-Commutative-Ring 0-cRing
is-trivial-0-cRing = refl
```

To-do: complete proof of uniqueness of the zero ring using SIP, ideally refactor
code to do zero algebras all along the chain to prettify and streamline future
work
