# Quasigroups

```agda
module group-theory.quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.left-quasigroups
open import group-theory.right-quasigroups
```

</details>

## Idea

{{#concept "Quasigroups" Agda=Quasigroup}} are [sets](foundation-core.sets.md) -
say, `Q` - equipped with three binary operations - say, `*`, `/`, `\` - such
that for `x y : type-Set Q`, the following hold:

```text
  y ＝ (y r/ x) * x
  y ＝ (y * x) r/ x
  y ＝ x * (x l/ y)
  y ＝ x l/ (x * y)
```

Roughly speaking, quasigroups are nonassociative semigroups, and in fact groups
are just pointed associative quasigroups.

## Definitions

### Left and right quasigroups

#### Left quasigroups

```agda
module _
  {l : Level} (Q : Set l) (mul left-div : type-Set Q → type-Set Q → type-Set Q)
  where

  private

    Q' : UU l
    Q' = type-Set Q

    Q'-is-set : is-set Q'
    Q'-is-set = is-set-type-Set Q

    _l/_ : Q' → Q' → Q'
    _l/_ = left-div

    _*_ : Q' → Q' → Q'
    _*_ = mul

  is-left-cancellative-left-div : UU l
  is-left-cancellative-left-div = (x y : Q') → y ＝ (x * (x l/ y))

  is-prop-is-left-cancellative-left-div : is-prop is-left-cancellative-left-div
  is-prop-is-left-cancellative-left-div =
    is-prop-Π λ x → is-prop-Π (λ y → Q'-is-set y (x * (x l/ y)))

  is-right-cancellative-left-div : UU l
  is-right-cancellative-left-div = (x y : Q') → y ＝ (x l/ (x * y))

  is-prop-is-right-cancellative-left-div :
    is-prop is-right-cancellative-left-div
  is-prop-is-right-cancellative-left-div =
    is-prop-Π λ x → is-prop-Π (λ y → Q'-is-set y (x l/ (x * y)))

  is-left-Quasigroup : UU l
  is-left-Quasigroup =
    is-left-cancellative-left-div × is-right-cancellative-left-div

  is-prop-is-left-Quasigroup : is-prop is-left-Quasigroup
  is-prop-is-left-Quasigroup =
    is-prop-Σ is-prop-is-left-cancellative-left-div
    (λ _ → is-prop-is-right-cancellative-left-div)

left-Quasigroup : (l : Level) → UU (lsuc l)
left-Quasigroup l =
  Σ (Set l) λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ mul → Σ (type-Set Q → type-Set Q → type-Set Q) (λ left-div →
  is-left-cancellative-left-div Q mul left-div ×
  is-right-cancellative-left-div Q mul left-div))
```

#### Right quasigroups

```agda
module _
  {l : Level} (Q : Set l) (mul right-div : type-Set Q → type-Set Q → type-Set Q)
  where

  private

    Q' : UU l
    Q' = type-Set Q

    Q'-is-set : is-set Q'
    Q'-is-set = is-set-type-Set Q

    _r/_ : Q' → Q' → Q'
    _r/_ = right-div

    _*_ : Q' → Q' → Q'
    _*_ = mul

  is-left-cancellative-right-div : UU l
  is-left-cancellative-right-div = (x y : Q') → y ＝ ((y r/ x) * x)

  is-prop-is-left-cancellative-right-div :
    is-prop is-left-cancellative-right-div
  is-prop-is-left-cancellative-right-div =
    is-prop-Π λ x → is-prop-Π (λ y → Q'-is-set y ((y r/ x) * x))

  is-right-cancellative-right-div : UU l
  is-right-cancellative-right-div = (x y : Q') → y ＝ ((y * x) r/ x)

  is-prop-is-right-cancellative-right-div :
    is-prop is-right-cancellative-right-div
  is-prop-is-right-cancellative-right-div =
    is-prop-Π λ x → is-prop-Π (λ y → Q'-is-set y ((y * x) r/ x))

  is-right-Quasigroup : UU l
  is-right-Quasigroup =
    is-left-cancellative-right-div × is-right-cancellative-right-div

  is-prop-is-right-Quasigroup : is-prop is-right-Quasigroup
  is-prop-is-right-Quasigroup =
    is-prop-Σ is-prop-is-left-cancellative-right-div
    λ _ → is-prop-is-right-cancellative-right-div

right-Quasigroup : (l : Level) → UU (lsuc l)
right-Quasigroup l =
  Σ (Set l) λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ right-div → is-right-Quasigroup Q mul right-div))
```

#### Quasigroups

A **quasigroup** is both a left and right quasigroup, with compatible
multiplication.

```agda
Quasigroup : (l : Level) → UU (lsuc l)
Quasigroup l =
  Σ (Set l) λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ left-div → Σ (type-Set Q → type-Set Q → type-Set Q) (λ right-div →
  is-left-Quasigroup Q mul left-div × is-right-Quasigroup Q mul right-div)))

module _
  {l : Level} (Q : Quasigroup l)
  where

  set-Quasigroup : Set l
  set-Quasigroup = pr1 Q

  type-Quasigroup : UU l
  type-Quasigroup = type-Set set-Quasigroup

  is-set-Quasigroup : is-set type-Quasigroup
  is-set-Quasigroup = is-set-type-Set set-Quasigroup

  mul-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  mul-Quasigroup = pr1 (pr2 Q)

  left-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  left-div-Quasigroup = pr1 (pr2 (pr2 Q))

  right-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  right-div-Quasigroup = pr1 (pr2 (pr2 (pr2 Q)))

  is-left-cancellative-left-div-Quasigroup :
    is-left-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-left-cancellative-left-div-Quasigroup = pr1 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-left-div-Quasigroup :
    is-right-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-right-cancellative-left-div-Quasigroup =
    pr2 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-left-cancellative-right-div-Quasigroup :
    is-left-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-left-cancellative-right-div-Quasigroup =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-right-div-Quasigroup :
    is-right-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-right-cancellative-right-div-Quasigroup =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))
```

## External links

- [Wikipedia](https://en.m.wikipedia.org/w/index.php?title=Quasigroup&oldid=1268215307)
