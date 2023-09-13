# Function extensionality

```agda
module foundation.function-extensionality where

open import foundation-core.function-extensionality public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

The function extensionality axiom asserts that identifications of (dependent)
functions are equivalently described as pointwise equalities between them. In
other words, a function is completely determined by its values.

In this file we postulate the function extensionality axiom. Its statement is
defined in
[`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).

## Postulate

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  postulate funext : (f : (x : A) → B x) → function-extensionality f
```

### Components of `funext`

```agda
  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext) = htpy-eq
  pr2 (equiv-funext {f} {g}) = funext f g

  eq-htpy : {f g : (x : A) → B x} → (f ~ g) → f ＝ g
  eq-htpy {f} {g} = map-inv-is-equiv (funext f g)

  abstract
    is-section-eq-htpy :
      {f g : (x : A) → B x} → (htpy-eq ∘ eq-htpy {f} {g}) ~ id
    is-section-eq-htpy {f} {g} = is-section-map-inv-is-equiv (funext f g)

    is-retraction-eq-htpy :
      {f g : (x : A) → B x} → (eq-htpy ∘ htpy-eq {f = f} {g = g}) ~ id
    is-retraction-eq-htpy {f} {g} = is-retraction-map-inv-is-equiv (funext f g)

    is-equiv-eq-htpy :
      (f g : (x : A) → B x) → is-equiv (eq-htpy {f} {g})
    is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext f g)

    eq-htpy-refl-htpy :
      (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
    eq-htpy-refl-htpy f = is-retraction-eq-htpy refl

    equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
    pr1 (equiv-eq-htpy {f} {g}) = eq-htpy
    pr2 (equiv-eq-htpy {f} {g}) = is-equiv-eq-htpy f g
```

## Properties

### `htpy-eq` preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  htpy-eq-concat :
    (p : f ＝ g) (q : g ＝ h) → htpy-eq (p ∙ q) ＝ (htpy-eq p ∙h htpy-eq q)
  htpy-eq-concat refl refl = refl
```

### `eq-htpy` preserves concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  eq-htpy-concat-htpy :
    (H : f ~ g) (K : g ~ h) → eq-htpy (H ∙h K) ＝ ((eq-htpy H) ∙ (eq-htpy K))
  eq-htpy-concat-htpy H K =
    equational-reasoning
      eq-htpy (H ∙h K)
      ＝ eq-htpy (htpy-eq (eq-htpy H) ∙h htpy-eq (eq-htpy K))
        by
        inv
          ( ap eq-htpy
            ( ap-binary _∙h_ (is-section-eq-htpy H) (is-section-eq-htpy K)))
      ＝ eq-htpy (htpy-eq (eq-htpy H ∙ eq-htpy K))
        by
        ap eq-htpy (inv (htpy-eq-concat (eq-htpy H) (eq-htpy K)))
      ＝ eq-htpy H ∙ eq-htpy K
        by
        is-retraction-eq-htpy (eq-htpy H ∙ eq-htpy K)
```

## See also

- That the univalence axiom implies function extensionality is proven in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
