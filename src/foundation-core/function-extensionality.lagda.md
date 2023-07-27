# Function extensionality

```agda
module foundation-core.function-extensionality where
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

## Statement

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  htpy-eq : {f g : (x : A) → B x} → (f ＝ g) → (f ~ g)
  htpy-eq refl = refl-htpy

  FUNEXT : (f : (x : A) → B x) → UU (l1 ⊔ l2)
  FUNEXT f = (g : (x : A) → B x) → is-equiv (htpy-eq {f} {g})
```

## Postulate

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  postulate funext : (f : (x : A) → B x) → FUNEXT f
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

### Naturality of `htpy-eq`

```agda
square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → g y ＝ h y) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl
```

### The action on paths of an evaluation map

```agda
ap-ev :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (a : A) → {f g : A → B} →
  (p : f ＝ g) → (ap (λ h → h a) p) ＝ htpy-eq p a
ap-ev a refl = refl
```

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
