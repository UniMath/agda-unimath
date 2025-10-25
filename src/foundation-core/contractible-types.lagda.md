# Contractible types

```agda
module foundation-core.contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Contractible types are types that have, up to identification, exactly one
element.

## Definition

```agda
is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center (pair c is-contr-A) = c

eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → x ＝ y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → x ＝ y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (x : A) → (center is-contr-A) ＝ x
  contraction C x = eq-is-contr C

  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (contraction is-contr-A (center is-contr-A)) ＝ refl
  coh-contraction (pair c C) = left-inv (C c)
```

## Properties

### Retracts of contractible types are contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-retract-of : A retract-of B → is-contr B → is-contr A
    pr1 (is-contr-retract-of (pair i (pair r is-retraction-r)) H) = r (center H)
    pr2 (is-contr-retract-of (pair i (pair r is-retraction-r)) H) x =
      ap r (contraction H (i x)) ∙ (is-retraction-r x)
```

### Contractible types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv f is-equiv-f =
      is-contr-retract-of B (f , retraction-is-equiv is-equiv-f)

  abstract
    is-contr-equiv : A ≃ B → is-contr B → is-contr A
    is-contr-equiv (e , is-equiv-e) is-contr-B =
      is-contr-is-equiv e is-equiv-e is-contr-B

module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f is-equiv-f is-contr-A =
      is-contr-is-equiv A
        ( map-inv-is-equiv is-equiv-f)
        ( is-equiv-map-inv-is-equiv is-equiv-f)
        ( is-contr-A)

  abstract
    is-contr-equiv' : (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (pair e is-equiv-e) is-contr-A =
      is-contr-is-equiv' e is-equiv-e is-contr-A

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr f is-contr-A is-contr-B =
      is-equiv-is-invertible
        ( λ y → center is-contr-A)
        ( λ y → eq-is-contr is-contr-B)
        ( contraction is-contr-A)

  equiv-is-contr : is-contr A → is-contr B → A ≃ B
  pr1 (equiv-is-contr is-contr-A is-contr-B) a = center is-contr-B
  pr2 (equiv-is-contr is-contr-A is-contr-B) =
    is-equiv-is-contr _ is-contr-A is-contr-B
```

### Contractibility of cartesian product types

Given two types `A` and `B`, the following are equivalent:

1. The type `A × B` is contractible.
2. Both `A` and `B` are contractible.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-left-factor-product : is-contr (A × B) → is-contr A
    is-contr-left-factor-product is-contr-AB =
      is-contr-retract-of
        ( A × B)
        ( pair
          ( λ x → pair x (pr2 (center is-contr-AB)))
          ( pair pr1 refl-htpy))
        ( is-contr-AB)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-right-factor-product : is-contr (A × B) → is-contr B
    is-contr-right-factor-product is-contr-AB =
      is-contr-retract-of
        ( A × B)
        ( pair
          ( pair (pr1 (center is-contr-AB)))
          ( pair pr2 refl-htpy))
        ( is-contr-AB)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-product : is-contr A → is-contr B → is-contr (A × B)
    pr1 (pr1 (is-contr-product (pair a C) (pair b D))) = a
    pr2 (pr1 (is-contr-product (pair a C) (pair b D))) = b
    pr2 (is-contr-product (pair a C) (pair b D)) (pair x y) =
      eq-pair (C x) (D y)
```

### Contractibility of Σ-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-contr-Σ' :
      is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
    pr1 (pr1 (is-contr-Σ' (pair a H) is-contr-B)) = a
    pr2 (pr1 (is-contr-Σ' (pair a H) is-contr-B)) = center (is-contr-B a)
    pr2 (is-contr-Σ' (pair a H) is-contr-B) (pair x y) =
      eq-pair-Σ
        ( inv (inv (H x)))
        ( eq-transpose-tr (inv (H x)) (eq-is-contr (is-contr-B a)))

  abstract
    is-contr-Σ :
      is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
    pr1 (pr1 (is-contr-Σ H a K)) = a
    pr2 (pr1 (is-contr-Σ H a K)) = center K
    pr2 (is-contr-Σ H a K) (pair x y) =
      eq-pair-Σ
        ( inv (eq-is-contr H))
        ( eq-transpose-tr (eq-is-contr H) (eq-is-contr K))
```

**Note**: In the previous construction, we showed that `Σ A B` is contractible
whenever `A` is contractible and whenever `B a` is contractible for a specified
term `a : A`. We _could_ have chosen this term `a` to be the center of
contraction of `A`. However, it turns out to be better not to do so in the
construction of `is-contr-Σ`. The reason is that proofs of contractibility could
be quite complicated and difficult to normalize. If we would require in the
definition of `is-contr-Σ` that `B (center c)` is contractible, given the proof
`c` of contractibility of `A`, then the type inference algorithm of Agda will be
forced to normalize the proof `c` including the contraction. By instead
providing a center of contraction by hand, we avoid this unnecessary load on the
type inference algorithm, and hence any instance of `is-contr-Σ` will type check
more efficiently.

The general theme is that it may be computationally expensive to extract
information from proofs of propositions, such as the center of contraction of a
proof of contractibility. The reason for that is that when Agda normalizes an
element (as it inevitably will do sometimes) then in such cases it will not just
normalize the extracted information (in this case the first projection of the
proof of contractibility), but it will normalize the entire proof of
contractibility first, and then apply the projection.

### Contractibility of the base of a contractible dependent sum

Given a type `A` and a type family over it `B`, then if the dependent sum
`Σ A B` is contractible and there is a section `(x : A) → B x`, then `A` is
contractible.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    is-contr-base-is-contr-Σ' :
      ((x : A) → B x) → is-contr (Σ A B) → is-contr A
    is-contr-base-is-contr-Σ' s =
      is-contr-retract-of (Σ A B) ((λ a → a , s a) , pr1 , refl-htpy)
```

### Contractible types are propositions

```agda
is-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (x ＝ y)
pr1 (is-prop-is-contr H x y) = eq-is-contr H
pr2 (is-prop-is-contr H x .x) refl = left-inv (pr2 H x)
```

### Products of families of contractible types are contractible

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  pr1 (is-contr-Π {A = A} {B = B} H) x = center (H x)
  pr2 (is-contr-Π {A = A} {B = B} H) f =
    eq-htpy (λ x → contraction (H x) (f x))

abstract
  is-contr-implicit-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ({x : A} → B x)
  is-contr-implicit-Π H =
    is-contr-equiv _ equiv-explicit-implicit-Π (is-contr-Π H)
```

### The type of functions into a contractible type is contractible

```agda
is-contr-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-contr B → is-contr (A → B)
is-contr-function-type is-contr-B = is-contr-Π (λ _ → is-contr-B)
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr (pair a α) (pair b β) =
    is-contr-Σ
      ( is-contr-function-type (pair b β))
      ( λ x → b)
      ( is-contr-product
        ( is-contr-Σ
          ( is-contr-function-type (pair a α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (pair b β) b)))
        ( is-contr-Σ
          ( is-contr-function-type (pair a α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (pair a α) a))))
```

### Being contractible is a proposition

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr (pair a α) =
      is-contr-Σ
        ( pair a α)
        ( a)
        ( is-contr-Π (is-prop-is-contr (pair a α) a))

  abstract
    is-property-is-contr : (H K : is-contr A) → is-contr (H ＝ K)
    is-property-is-contr H = is-prop-is-contr (is-contr-is-contr H) H
```
