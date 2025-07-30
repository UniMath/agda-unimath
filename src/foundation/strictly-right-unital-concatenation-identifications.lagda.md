# The strictly right unital concatenation operation on identifications

```agda
module foundation.strictly-right-unital-concatenation-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The concatenation operation on
[identifications](foundation-core.identity-types.md) is a family of binary
operations

```text
  _∙_ : x ＝ y → y ＝ z → x ＝ z
```

indexed by `x y z : A`. However, there are essentially three different ways we
can define concatenation of identifications, all with different computational
behaviors:

1. We can define concatenation by induction on the equality `x ＝ y`. This gives
   us the computation rule `refl ∙ q ≐ q`.
2. We can define concatenation by induction on the equality `y ＝ z`. This gives
   us the computation rule `p ∙ refl ≐ p`.
3. We can define concatenation by induction on both `x ＝ y` and `y ＝ z`. This
   only gives us the computation rule `refl ∙ refl ≐ refl`.

While the third option may be preferred by some for its symmetry, for practical
reasons, we prefer one of the first two, and by convention we use the first
alternative. However, there are cases where the second case may be preferred.
Hence why we on this page consider the
{{#concept "strictly right unital concatenation operation on identifications" Agda=_∙ᵣ_ Agda=right-strict-concat Agda=right-strict-concat'}}.

This definition is for instance used with the
[strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
to construct a strictly left unital concatenation operation.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣ_
  _∙ᵣ_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  p ∙ᵣ refl = p

  right-strict-concat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  right-strict-concat p z q = p ∙ᵣ q

  right-strict-concat' : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  right-strict-concat' x q p = p ∙ᵣ q
```

### Translating between the strictly left and strictly right unital versions of concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  eq-right-strict-concat-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙ᵣ q
  eq-right-strict-concat-concat p refl = right-unit

  eq-concat-right-strict-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ∙ᵣ q ＝ p ∙ q
  eq-concat-right-strict-concat p q = inv (eq-right-strict-concat-concat p q)

  eq-double-right-strict-concat-concat-left-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    (p ∙ q) ∙ r ＝ (p ∙ᵣ q) ∙ᵣ r
  eq-double-right-strict-concat-concat-left-associated p q r =
    ( ap (_∙ r) (eq-right-strict-concat-concat p q)) ∙
    ( eq-right-strict-concat-concat (p ∙ᵣ q) r)

  eq-double-right-strict-concat-concat-right-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ (q ∙ r) ＝ p ∙ᵣ (q ∙ᵣ r)
  eq-double-right-strict-concat-concat-right-associated p q r =
    ( ap (p ∙_) (eq-right-strict-concat-concat q r)) ∙
    ( eq-right-strict-concat-concat p (q ∙ᵣ r))

  eq-double-concat-right-strict-concat-left-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    (p ∙ᵣ q) ∙ᵣ r ＝ (p ∙ q) ∙ r
  eq-double-concat-right-strict-concat-left-associated p q r =
    ( ap (_∙ᵣ r) (eq-concat-right-strict-concat p q)) ∙
    ( eq-concat-right-strict-concat (p ∙ q) r)

  eq-double-concat-right-strict-concat-right-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ᵣ (q ∙ᵣ r) ＝ p ∙ (q ∙ r)
  eq-double-concat-right-strict-concat-right-associated p q r =
    ( ap (p ∙ᵣ_) (eq-concat-right-strict-concat q r)) ∙
    ( eq-concat-right-strict-concat p (q ∙ r))
```

## Properties

### The groupoidal laws

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-right-strict-concat :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    ((p ∙ᵣ q) ∙ᵣ r) ＝ (p ∙ᵣ (q ∙ᵣ r))
  assoc-right-strict-concat p q refl = refl

  left-unit-right-strict-concat : {x y : A} {p : x ＝ y} → refl ∙ᵣ p ＝ p
  left-unit-right-strict-concat {p = refl} = refl

  right-unit-right-strict-concat : {x y : A} {p : x ＝ y} → p ∙ᵣ refl ＝ p
  right-unit-right-strict-concat = refl

  left-inv-right-strict-concat : {x y : A} (p : x ＝ y) → inv p ∙ᵣ p ＝ refl
  left-inv-right-strict-concat refl = refl

  right-inv-right-strict-concat : {x y : A} (p : x ＝ y) → p ∙ᵣ inv p ＝ refl
  right-inv-right-strict-concat refl = refl

  inv-inv-right-strict-concat : {x y : A} (p : x ＝ y) → inv (inv p) ＝ p
  inv-inv-right-strict-concat refl = refl

  distributive-inv-right-strict-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    inv (p ∙ᵣ q) ＝ inv q ∙ᵣ inv p
  distributive-inv-right-strict-concat refl refl = refl
```

### Transposing inverses

```agda
module _
  {l : Level} {A : UU l}
  where

  left-transpose-eq-right-strict-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ᵣ q ＝ r → q ＝ inv p ∙ᵣ r
  left-transpose-eq-right-strict-concat refl q r s =
    (inv left-unit-right-strict-concat ∙ s) ∙ inv left-unit-right-strict-concat

  right-transpose-eq-right-strict-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ᵣ q ＝ r → p ＝ r ∙ᵣ inv q
  right-transpose-eq-right-strict-concat p refl r s = s
```

### Concatenation is injective

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-injective-right-strict-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ᵣ q ＝ p ∙ᵣ r → q ＝ r
  is-injective-right-strict-concat refl s =
    (inv left-unit-right-strict-concat ∙ s) ∙ left-unit-right-strict-concat

  is-injective-right-strict-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → p ∙ᵣ r ＝ q ∙ᵣ r → p ＝ q
  is-injective-right-strict-concat' refl s = s
```

## See also

- [Yoneda identity types](foundation.yoneda-identity-types.md)
- [Computational identity types](foundation.computational-identity-types.md)
