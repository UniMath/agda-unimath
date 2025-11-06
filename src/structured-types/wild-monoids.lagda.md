# Wild monoids

```agda
module structured-types.wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "wild monoid" Agda=Wild-Monoid}} is a first–order approximation to
an ∞-monoid, i.e. a ∞-monoid-like structure whose laws hold at least up to the
first homotopy level, but may fail at higher levels.

A wild monoid consists of

- an underlying type `A`
- a unit, say `e : A`
- a binary operation on `A`, say `_*_`
- left and right unit laws `e * x ＝ x` and `x * e ＝ x`
- a coherence between the left and right unit laws at the unit
- an associator `(x y z : A) → (x * y) * z ＝ x * (y * z)`
- coherences between the associator and the left and right unit laws

We call such an associator **unital**. It may be described as a coherence of the
following diagram

```text
        map-associative-product
     (A × A) × A ----> A × (A × A)
             |           |
  (_*_ , id) |           | (id, _*_)
             ∨           ∨
           A × A       A × A
               \       /
          (_*_) \     / (_*_)
                 ∨   ∨
                   A
```

such that the three diagrams below cohere

```text
            associator
  (e * x) * y ===== e * (x * y)
          \\         //
     left  \\       //  left
   unit law \\     // unit law
              y * z,
```

```text
            associator
  (x * e) * y ===== x * (e * y)
          \\         //
    right  \\       //  left
   unit law \\     // unit law
              x * y,
```

and

```text
            associator
  (x * y) * e ===== x * (y * e)
          \\         //
    right  \\       //  right
   unit law \\     // unit law
              x * y
```

for all `x y : A`.

Concretely, we define wild monoids to be
[H-spaces](structured-types.h-spaces.md) equipped with a unital associator.

## Definition

### Unital associators on H-spaces

```agda
module _
  {l : Level} (M : H-Space l)
  where

  associator-H-Space : UU l
  associator-H-Space =
    (x y z : type-H-Space M) →
    mul-H-Space M (mul-H-Space M x y) z ＝
    mul-H-Space M x (mul-H-Space M y z)

  is-unital-associator : (α : associator-H-Space) → UU l
  is-unital-associator α111 =
    Σ ( (y z : type-H-Space M) →
        ( α111 (unit-H-Space M) y z) ∙
        ( left-unit-law-mul-H-Space M (mul-H-Space M y z)) ＝
        ( ap (mul-H-Space' M z) (left-unit-law-mul-H-Space M y)))
      ( λ α011 →
        Σ ( (x z : type-H-Space M) →
            ( α111 x (unit-H-Space M) z) ∙
            ( ap (mul-H-Space M x) (left-unit-law-mul-H-Space M z)) ＝
            ( ap (mul-H-Space' M z) (right-unit-law-mul-H-Space M x)))
          ( λ α101 →
            Σ ( (x y : type-H-Space M) →
                ( α111 x y (unit-H-Space M)) ∙
                ( ap (mul-H-Space M x) (right-unit-law-mul-H-Space M y)) ＝
                ( right-unit-law-mul-H-Space M (mul-H-Space M x y)))
              ( λ α110 → unit)))

  unital-associator : UU l
  unital-associator = Σ (associator-H-Space) (is-unital-associator)
```

### Wild monoids

```agda
Wild-Monoid : (l : Level) → UU (lsuc l)
Wild-Monoid l =
  Σ (H-Space l) unital-associator

module _
  {l : Level} (M : Wild-Monoid l)
  where

  h-space-Wild-Monoid : H-Space l
  h-space-Wild-Monoid = pr1 M

  type-Wild-Monoid : UU l
  type-Wild-Monoid = type-H-Space h-space-Wild-Monoid

  unit-Wild-Monoid : type-Wild-Monoid
  unit-Wild-Monoid = unit-H-Space h-space-Wild-Monoid

  pointed-type-Wild-Monoid : Pointed-Type l
  pointed-type-Wild-Monoid =
    pointed-type-H-Space h-space-Wild-Monoid

  coherent-unital-mul-Wild-Monoid :
    coherent-unital-mul-Pointed-Type pointed-type-Wild-Monoid
  coherent-unital-mul-Wild-Monoid =
    coherent-unital-mul-H-Space h-space-Wild-Monoid

  mul-Wild-Monoid : type-Wild-Monoid → type-Wild-Monoid → type-Wild-Monoid
  mul-Wild-Monoid = mul-H-Space h-space-Wild-Monoid

  mul-Wild-Monoid' : type-Wild-Monoid → type-Wild-Monoid → type-Wild-Monoid
  mul-Wild-Monoid' = mul-H-Space' h-space-Wild-Monoid

  ap-mul-Wild-Monoid :
    {a b c d : type-Wild-Monoid} →
    a ＝ b → c ＝ d → mul-Wild-Monoid a c ＝ mul-Wild-Monoid b d
  ap-mul-Wild-Monoid = ap-mul-H-Space h-space-Wild-Monoid

  left-unit-law-mul-Wild-Monoid :
    (x : type-Wild-Monoid) → mul-Wild-Monoid unit-Wild-Monoid x ＝ x
  left-unit-law-mul-Wild-Monoid =
    left-unit-law-mul-H-Space h-space-Wild-Monoid

  right-unit-law-mul-Wild-Monoid :
    (x : type-Wild-Monoid) → mul-Wild-Monoid x unit-Wild-Monoid ＝ x
  right-unit-law-mul-Wild-Monoid =
    right-unit-law-mul-H-Space h-space-Wild-Monoid

  coh-unit-laws-mul-Wild-Monoid :
    ( left-unit-law-mul-Wild-Monoid unit-Wild-Monoid) ＝
    ( right-unit-law-mul-Wild-Monoid unit-Wild-Monoid)
  coh-unit-laws-mul-Wild-Monoid =
    coh-unit-laws-mul-H-Space h-space-Wild-Monoid

  unital-associator-Wild-Monoid :
    unital-associator h-space-Wild-Monoid
  unital-associator-Wild-Monoid = pr2 M

  associator-Wild-Monoid :
    associator-H-Space h-space-Wild-Monoid
  associator-Wild-Monoid = pr1 unital-associator-Wild-Monoid

  associative-mul-Wild-Monoid :
    (x y z : type-Wild-Monoid) →
    ( mul-Wild-Monoid (mul-Wild-Monoid x y) z) ＝
    ( mul-Wild-Monoid x (mul-Wild-Monoid y z))
  associative-mul-Wild-Monoid = pr1 unital-associator-Wild-Monoid

  unit-law-110-associative-Wild-Monoid :
    (x y : type-Wild-Monoid) →
    ( associative-mul-Wild-Monoid x y unit-Wild-Monoid) ∙
    ( ap (mul-Wild-Monoid x) (right-unit-law-mul-Wild-Monoid y)) ＝
    ( right-unit-law-mul-Wild-Monoid (mul-Wild-Monoid x y))
  unit-law-110-associative-Wild-Monoid = pr1 (pr2 (pr2 (pr2 (pr2 M))))
```
