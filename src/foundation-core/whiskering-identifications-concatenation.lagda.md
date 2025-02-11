# Whiskering identifications with respect to concatenation

```agda
module foundation-core.whiskering-identifications-concatenation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels
open import foundation.whiskering-operations

open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Consider two [identifications](foundation-core.identity-types.md) `p q : x ＝ y`
in a type `A`. The whiskering operations are operations that take
identifications `p ＝ q` to identifications `r ∙ p ＝ r ∙ q` or to
identifications `p ∙ r ＝ q ∙ r`.

The
{{#concept "left whiskering" Disambiguation="identifications" Agda=left-whisker-concat}}
operation takes an identification `r : z ＝ x` and an identification `p ＝ q` to
an identification `r ∙ p ＝ r ∙ q`. Similarly, the
{{#concept "right whiskering" Disambiguation="identifications" Agda=right-whisker-concat}}
operation takes an identification `r : y ＝ z` and an identification `p ＝ q` to
an identification `p ∙ r ＝ q ∙ r`.

The whiskering operations can be defined by the
[acion on identifications](foundation.action-on-identifications-functions.md) of
concatenation. Since concatenation on either side is an
[equivalence](foundation-core.equivalences.md), it follows that the whiskering
operations are equivalences.

## Definitions

### Left whiskering of identifications

Left whiskering of identifications with respect to concatenation is an operation

```text
  (p : x ＝ y) {q r : y ＝ z} → q ＝ r → p ∙ q ＝ p ∙ r
```

on any type.

```agda
module _
  {l : Level} {A : UU l}
  where

  left-whisker-concat : left-whiskering-operation A (_＝_) (_∙_) (_＝_)
  left-whisker-concat p β = ap (p ∙_) β

  left-unwhisker-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ q ＝ p ∙ r → q ＝ r
  left-unwhisker-concat = is-injective-concat
```

### Right whiskering of identifications

Right whiskering of identifications with respect to concatenation is an
operation

```text
  {p q : x ＝ y} → p ＝ q → (r : y ＝ z) → p ∙ r ＝ q ∙ r
```

on any type.

```agda
module _
  {l : Level} {A : UU l}
  where

  right-whisker-concat : right-whiskering-operation A (_＝_) (_∙_) (_＝_)
  right-whisker-concat α q = ap (_∙ q) α

  right-unwhisker-concat :
    {x y z : A} {p q : x ＝ y} (r : y ＝ z) → p ∙ r ＝ q ∙ r → p ＝ q
  right-unwhisker-concat r = is-injective-concat' r
```

### Double whiskering of identifications

```agda
module _
  {l : Level} {A : UU l}
  {a b c d : A} (p : a ＝ b) {r s : b ＝ c} (t : r ＝ s) (q : c ＝ d)
  where

  double-whisker-concat : (p ∙ r) ∙ q ＝ (p ∙ s) ∙ q
  double-whisker-concat = right-whisker-concat (left-whisker-concat p t) q

  double-whisker-concat' : p ∙ (r ∙ q) ＝ p ∙ (s ∙ q)
  double-whisker-concat' = left-whisker-concat p (right-whisker-concat t q)
```

## Properties

### The unit and absorption laws for left whiskering of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  left-unit-law-left-whisker-concat :
    {x y : A} {p p' : x ＝ y} (α : p ＝ p') →
    left-whisker-concat refl α ＝ α
  left-unit-law-left-whisker-concat refl = refl

  right-absorption-law-left-whisker-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-concat p (refl {x = q}) ＝ refl
  right-absorption-law-left-whisker-concat p q = refl
```

### The unit and absorption laws for right whiskering of identifications

The right unit law for right whiskering of identifications with respect to
concatenation asserts that the square of identifications

```text
                     right-whisker-concat α refl
           p ∙ refl -----------------------------> p' ∙ refl
             |                                        |
  right-unit |                                        |
             ∨                                        ∨
             p -------------------------------------> p'
```

commutes for any `α : p ＝ p'`. Note that this law is slightly more complicated,
since concatenating with `refl` on the right does not compute to the identity
function.

```agda
module _
  {l : Level} {A : UU l}
  where

  right-unit-law-right-whisker-concat :
    {x y : A} {p p' : x ＝ y} (α : p ＝ p') →
    right-unit ∙ α ＝ right-whisker-concat α refl ∙ right-unit
  right-unit-law-right-whisker-concat {p = refl} refl = refl

  left-absorption-law-right-whisker-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    right-whisker-concat (refl {x = p}) q ＝ refl
  left-absorption-law-right-whisker-concat p q = refl
```

### Commutativity of left and right whiskering of identifications

Consider four identifications `p p' : x ＝ y` and `q q' : y ＝ z` in a type `A`.
Then the square of identifications

```text
                         right-whisker α q
                 p ∙ q ---------------------> p' ∙ q
                   |                             |
  left-whisker p β |                             | left-whisker p' β
                   ∨                             ∨
                 p ∙ q' --------------------> p' ∙ q'
                         right-whisker α q'
```

commutes. There are at least two natural ways in which this square is seen to
commute:

1. The square commutes by naturality of the homotopy
   `p ↦ left-whisker-concat p β`.
2. The transposed square commutes by the naturality of the homotopy
   `q ↦ right-whisker-concat α q`.

The first way can be thought of as braiding `β` over `α`, while the second can
be thought of braiding `α` under `β`. Braiding `β` over `α`, then braiding `α`
under `β` results in no braid at all. Thus, these two ways in which the square
commutes are inverse to each other.

**Note.** The following statements could have been formalized using
[commuting squares of identifications](foundation.commuting-squares-of-identifications.md).
However, in order to avoid cyclic module dependencies in the library we avoid
doing so.

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p p' : x ＝ y} {q q' : y ＝ z}
  where

  commutative-left-whisker-right-whisker-concat :
    (β : q ＝ q') (α : p ＝ p') →
    left-whisker-concat p β ∙ right-whisker-concat α q' ＝
    right-whisker-concat α q ∙ left-whisker-concat p' β
  commutative-left-whisker-right-whisker-concat β =
    nat-htpy (λ p → left-whisker-concat p β)

  commutative-right-whisker-left-whisker-concat :
    (α : p ＝ p') (β : q ＝ q') →
    right-whisker-concat α q ∙ left-whisker-concat p' β ＝
    left-whisker-concat p β ∙ right-whisker-concat α q'
  commutative-right-whisker-left-whisker-concat α =
    nat-htpy (right-whisker-concat α)

  compute-inv-commutative-right-whisker-left-whisker-concat :
    (β : q ＝ q') (α : p ＝ p') →
    ( inv (commutative-right-whisker-left-whisker-concat α β)) ＝
    ( commutative-left-whisker-right-whisker-concat β α)
  compute-inv-commutative-right-whisker-left-whisker-concat refl refl =
    refl
```

### Swapping the order of left and right whiskering of identifications

Consider a diagram of identifications

```text
               r
      p      ----->     q
  a -----> b -----> c ----->
               s
```

with `t : r ＝ s`. Then the square of identifications

```text
                               assoc p r q
                  (p ∙ r) ∙ q -------------> p ∙ (r ∙ q)
                       |                          |
  double-whisker p t q |                          | double-whisker' p t q
                       ∨                          ∨
                  (p ∙ s) ∙ q -------------> p ∙ (s ∙ q)
                               assoc p s q
```

commutes.

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  swap-double-whisker-concat :
    {a b c d : A} (p : a ＝ b) {r s : b ＝ c} (t : r ＝ s) (q : c ＝ d) →
    double-whisker-concat p t q ∙ assoc p s q ＝
    assoc p r q ∙ double-whisker-concat' p t q
  swap-double-whisker-concat refl refl refl = refl
```

### The action on identifications of concatenating by `refl` on the right

Consider an identification `r : p ＝ q` between two identifications
`p q : x ＝ y` in a type `A`. Then the square of identifications

```text
                      right-whisker r refl
            p ∙ refl ----------------------> q ∙ refl
              |                                |
   right-unit |                                | right-unit
              ∨                                ∨
              p -----------------------------> q
                                r
```

commutes.

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y}
  where

  compute-refl-right-whisker-concat :
    (r : p ＝ q) →
    right-unit ∙ r ＝ right-whisker-concat r refl ∙ right-unit
  compute-refl-right-whisker-concat refl = right-unit
```

### Left whiskering of identifications distributes over concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  distributive-left-whisker-concat-concat :
    {a b c : A} (p : a ＝ b) {q r s : b ＝ c} (α : q ＝ r) (β : r ＝ s) →
    left-whisker-concat p (α ∙ β) ＝
    left-whisker-concat p α ∙ left-whisker-concat p β
  distributive-left-whisker-concat-concat p refl β = refl
```

### Right whiskering of identifications distributes over concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  distributive-right-whisker-concat-concat :
    {a b c : A} {p q r : a ＝ b} (α : p ＝ q) (β : q ＝ r) (s : b ＝ c) →
    right-whisker-concat (α ∙ β) s ＝
    right-whisker-concat α s ∙ right-whisker-concat β s
  distributive-right-whisker-concat-concat refl β s = refl
```

### Left whiskering of identifications commutes with inverses of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-inv-left-whisker-concat :
    {a b c : A} (p : a ＝ b) {q r : b ＝ c} (s : q ＝ r) →
    left-whisker-concat p (inv s) ＝ inv (left-whisker-concat p s)
  compute-inv-left-whisker-concat p s = ap-inv (concat p _) s
```

### Right whiskering of identifications commutes with inverses of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-inv-right-whisker-concat :
    {a b c : A} {p q : a ＝ b} (s : p ＝ q) (r : b ＝ c) →
    right-whisker-concat (inv s) r ＝ inv (right-whisker-concat s r)
  compute-inv-right-whisker-concat s r = ap-inv (concat' _ r) s
```
