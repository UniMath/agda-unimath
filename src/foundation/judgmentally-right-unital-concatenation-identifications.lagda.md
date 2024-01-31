# The judgmentally right unital concatenation operation on identifications

```agda
module foundation.judgmentally-right-unital-concatenation-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The
{{#concept "concatenation operation on identifications" Agda=_∙_ Agda=_∙'_ Agda=concat}}
is a map

```text
  _∙_ : x ＝ y → y ＝ z → x ＝ z
```

for all `x y z : A`. However, there are essentially three different ways we can
define concatenation of identifications, all with different computational
behaviours.

1. We can define concatenation by induction on the equality `x ＝ y`. This gives
   us the computation rule `refl ∙ q = q`.
2. We can define concatenation by induction on the equality `y ＝ z`. This gives
   us the computation rule `p ∙ refl = p`.
3. We can define `_∙_` by induction on both `x ＝ y` and `y ＝ z`. This only
   gives us the computation rule `refl ∙ refl = refl`.

While the third option may be preferred by some for its symmetry, for practical
reasons, we use the first alternative by convention.

However, there are cases where the second case may be preferred. Hence, in this
file we consider the
{{#concept "definitionally right unital concatenation operation on identifications" Agda=_∙ᵣ_ Agda=rconcat Agda=rconcat'}}.

This definition is for instance used with the
[judgmentally involutive identity types](foundation.judgmentally-involutive-identity-types.md)
to construct a judgmentally left unital concatenation operation.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣ_
  _∙ᵣ_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  p ∙ᵣ refl = p

  rconcat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  rconcat p z q = p ∙ᵣ q

  rconcat' : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  rconcat' x q p = p ∙ᵣ q
```

### Translating between the left and right unital versions of concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  eq-rconcat-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙ᵣ q
  eq-rconcat-concat refl refl = refl

  eq-concat-rconcat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ∙ᵣ q ＝ p ∙ q
  eq-concat-rconcat p q = inv (eq-rconcat-concat p q)

  eq-double-rconcat-concat-left-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ q ∙ r ＝ p ∙ᵣ q ∙ᵣ r
  eq-double-rconcat-concat-left-associated p q r =
    ap (_∙ r) (eq-rconcat-concat p q) ∙ eq-rconcat-concat (p ∙ᵣ q) r

  eq-double-rconcat-concat-right-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ (q ∙ r) ＝ p ∙ᵣ (q ∙ᵣ r)
  eq-double-rconcat-concat-right-associated p q r =
    ap (p ∙_) (eq-rconcat-concat q r) ∙ eq-rconcat-concat p (q ∙ᵣ r)

  eq-double-concat-rconcat-left-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ᵣ q ∙ᵣ r ＝ p ∙ q ∙ r
  eq-double-concat-rconcat-left-associated p q r =
    ap (_∙ᵣ r) (eq-concat-rconcat p q) ∙ eq-concat-rconcat (p ∙ q) r

  eq-double-concat-rconcat-right-associated :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    p ∙ᵣ (q ∙ᵣ r) ＝ p ∙ (q ∙ r)
  eq-double-concat-rconcat-right-associated p q r =
    ap (p ∙ᵣ_) (eq-concat-rconcat q r) ∙ eq-concat-rconcat p (q ∙ r)
```

## Properties

### The groupoidal laws

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-rconcat :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    ((p ∙ᵣ q) ∙ᵣ r) ＝ (p ∙ᵣ (q ∙ᵣ r))
  assoc-rconcat p q refl = refl

  left-unit-rconcat : {x y : A} {p : x ＝ y} → refl ∙ᵣ p ＝ p
  left-unit-rconcat {p = refl} = refl

  right-unit-rconcat : {x y : A} {p : x ＝ y} → p ∙ᵣ refl ＝ p
  right-unit-rconcat = refl

  left-inv-rconcat : {x y : A} (p : x ＝ y) → inv p ∙ᵣ p ＝ refl
  left-inv-rconcat refl = refl

  right-inv-rconcat : {x y : A} (p : x ＝ y) → p ∙ᵣ (inv p) ＝ refl
  right-inv-rconcat refl = refl

  inv-inv-rconcat : {x y : A} (p : x ＝ y) → inv (inv p) ＝ p
  inv-inv-rconcat refl = refl

  distributive-inv-rconcat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    inv (p ∙ᵣ q) ＝ inv q ∙ᵣ inv p
  distributive-inv-rconcat refl refl = refl
```

### Transposing inverses

```agda
module _
  {l : Level} {A : UU l}
  where

  left-transpose-eq-rconcat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ᵣ q ＝ r → q ＝ inv p ∙ᵣ r
  left-transpose-eq-rconcat refl q r s =
    (inv left-unit-rconcat ∙ s) ∙ inv left-unit-rconcat

  right-transpose-eq-rconcat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ᵣ q ＝ r → p ＝ r ∙ᵣ inv q
  right-transpose-eq-rconcat p refl r s = s
```

### Concatenation is injective

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-injective-rconcat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ᵣ q ＝ p ∙ᵣ r → q ＝ r
  is-injective-rconcat refl s = (inv left-unit-rconcat ∙ s) ∙ left-unit-rconcat

  is-injective-rconcat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → p ∙ᵣ r ＝ q ∙ᵣ r → p ＝ q
  is-injective-rconcat' refl s = s
```
