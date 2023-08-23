# Identity types

```agda
module foundation-core.identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The equality relation on a type is a reflexive relation, with the universal
property that it maps uniquely into any other reflexive relation. In type
theory, we introduce the identity type as an inductive family of types, where
the induction principle can be understood as expressing that the identity type
is the least reflexive relation.

### Notation of the identity type

We include two notations for the identity type. First, we introduce the identity
type using Martin-Löf's original notation `Id`. Then we introduce as a secondary
option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign
on your keyboard, but it is the
[full width equals sign](https://codepoints.net/U+ff1d). Note that the full
width equals sign is slightly wider, and it is highlighted like all the other
defined constructions in Agda. In order to type the full width equals sign in
Agda's Emacs Mode, you need to add it to your agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full
width equals sign `＝`.

## List of files directly related to identity types

The following table lists files that are about identity types and operations on
identifications in arbitrary types.

| Concept                                          | File                                                                                                                      |
| ------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------- |
| Action on identifications of binary functions    | [`foundation.action-on-identifications-binary-functions`](foundation.action-on-identifications-binary-functions.md)       |
| Action on identifications of dependent functions | [`foundation.action-on-identifications-dependent-functions`](foundation.action-on-identifications-dependent-functions.md) |
| Action on identifications of functions           | [`foundation.action-on-identifications-functions`](foundation.action-on-identifications-functions.md)                     |
| Binary transport                                 | [`foundation.binary-transport`](foundation.binary-transport.md)                                                           |
| Commuting squares of identifications             | [`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md)                   |
| Dependent identifications (foundation)           | [`foundation.dependent-identifications`](foundation.dependent-identifications.md)                                         |
| Dependent identifications (foundation-core)      | [`foundation-core.dependent-identifications`](foundation-core.dependent-identifications.md)                               |
| The fundamental theorem of identity types        | [`foundation.fundamental-theorem-of-identity-types`](foundation.fundamental-theorem-of-identity-types.md)                 |
| Hexagons of identifications                      | [`foundation.hexagons-of-identifications`](foundation.hexagons-of-identifications.md)                                     |
| Identity systems                                 | [`foundation.identity-systems`](foundation.identity-systems.md)                                                           |
| The identity type (foundation)                   | [`foundation.identity-types`](foundation.identity-types.md)                                                               |
| The identity type (foundation-core)              | [`foundation-core.identity-types`](foundation-core.identity-types.md)                                                     |
| Large identity types                             | [`foundation.large-identity-types`](foundation.large-identity-types.md)                                                   |
| Path algebra                                     | [`foundation.path-algebra`](foundation.path-algebra.md)                                                                   |
| Symmetric identity types                         | [`foundation.symmetric-identity-types`](foundation.symmetric-identity-types.md)                                           |
| Torsorial type families                          | [`foundation.torsorial-type-families`](foundation.torsorial-type-families.md)                                             |
| Transport (foundation)                           | [`foundation.transport`](foundation.transport.md)                                                                         |
| Transport (foundation-core)                      | [`foundation-core.transport`](foundation-core.transport.md)                                                               |
| The universal property of identity types         | [`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md)                         |

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  data Id (x : A) : A → UU l where
    refl : Id x x

  _＝_ : A → A → UU l
  (a ＝ b) = Id a b

{-# BUILTIN EQUALITY Id #-}
```

### The induction principle

The induction principle of identity types states that given a base point `x : A`
and a family of types over the identity types based at `x`,
`B : (y : A) (p : x ＝ y) → UU l2`, then to construct a dependent function
`f : (y : A) (p : x ＝ y) → B y p` it suffices to define it at `f x refl`.

Note that Agda's pattern matching machinery allows us to define many operations
on the identity type directly. However, sometimes it is useful to explicitly
have the induction principle of the identity type.

```agda
ind-Id :
  {l1 l2 : Level} {A : UU l1}
  (x : A) (B : (y : A) (p : x ＝ y) → UU l2) →
  (B x refl) → (y : A) (p : x ＝ y) → B y p
ind-Id x B b y refl = b
```

## Structure

The identity types form a weak groupoidal structure on types.

### Concatenation of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  _∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  refl ∙ q = q

  concat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  concat p z q = p ∙ q

  concat' : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  concat' x q p = p ∙ q
```

### Inverting identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv : {x y : A} → x ＝ y → y ＝ x
  inv refl = refl
```

### The groupoidal laws for types

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    ((p ∙ q) ∙ r) ＝ (p ∙ (q ∙ r))
  assoc refl q r = refl

  left-unit : {x y : A} {p : x ＝ y} → (refl ∙ p) ＝ p
  left-unit = refl

  right-unit : {x y : A} {p : x ＝ y} → (p ∙ refl) ＝ p
  right-unit {p = refl} = refl

  left-inv : {x y : A} (p : x ＝ y) → ((inv p) ∙ p) ＝ refl
  left-inv refl = refl

  right-inv : {x y : A} (p : x ＝ y) → (p ∙ (inv p)) ＝ refl
  right-inv refl = refl

  inv-inv : {x y : A} (p : x ＝ y) → (inv (inv p)) ＝ p
  inv-inv refl = refl

  distributive-inv-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    (inv (p ∙ q)) ＝ ((inv q) ∙ (inv p))
  distributive-inv-concat refl refl = refl
```

### Transposing inverses

```agda
inv-con :
  {l : Level} {A : UU l} {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z)
  (r : x ＝ z) → ((p ∙ q) ＝ r) → q ＝ ((inv p) ∙ r)
inv-con refl q r s = s

con-inv :
  {l : Level} {A : UU l} {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z)
  (r : x ＝ z) → ((p ∙ q) ＝ r) → p ＝ (r ∙ (inv q))
con-inv p refl r s = ((inv right-unit) ∙ s) ∙ (inv right-unit)
```

The fact that `inv-con` and `con-inv` are equivalences is recorded in
[`foundation.identity-types`](foundation.identity-types.md).

### Concatenation is injective

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → (p ∙ q) ＝ (p ∙ r) → q ＝ r
  is-injective-concat refl s = s

  is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → (p ∙ r) ＝ (q ∙ r) → p ＝ q
  is-injective-concat' refl s = (inv right-unit) ∙ (s ∙ right-unit)
```

## Equational reasoning

Identifications can be constructed by equational reasoning in the following way:

```text
equational-reasoning
  x ＝ y by eq-1
    ＝ z by eq-2
    ＝ v by eq-3
```

The resulting identification of this computaion is `eq-1 ∙ (eq-2 ∙ eq-3)`, i.e.,
the identification is associated fully to the right. For examples of the use of
equational reasoning, see
[addition-integers](elementary-number-theory.addition-integers.md).

```agda
infixl 1 equational-reasoning_
infixl 0 step-equational-reasoning

equational-reasoning_ :
  {l : Level} {X : UU l} (x : X) → x ＝ x
equational-reasoning x = refl

step-equational-reasoning :
  {l : Level} {X : UU l} {x y : X} →
  (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)
step-equational-reasoning p z q = p ∙ q

syntax step-equational-reasoning p z q = p ＝ z by q
```

## References

Our setup of equational reasoning is derived from the following sources:

1. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda>

2. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda>

3. The Agda standard library.
   <https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda>
