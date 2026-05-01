# Homotopies

```agda
module foundation.homotopies where

open import foundation-core.homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-identifications
open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies-concatenation
```

</details>

## Idea

A homotopy of identifications is a pointwise equality between dependent
functions. We defined homotopies in
[`foundation-core.homotopies`](foundation-core.homotopies.md). In this file, we
record some properties of homotopies that require function extensionality,
equivalences, or other.

## Properties

### Inverting homotopies is an equivalence

```agda
is-equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
is-equiv-inv-htpy f g =
  is-equiv-is-invertible
    ( inv-htpy)
    ( λ H → eq-htpy (λ x → inv-inv (H x)))
    ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
pr1 (equiv-inv-htpy f g) = inv-htpy
pr2 (equiv-inv-htpy f g) = is-equiv-inv-htpy f g
```

### Concatenating homotopies by a fixed homotopy is an equivalence

#### Concatenating from the left

```agda
is-equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) →
  (h : (x : A) → B x) → is-equiv (concat-htpy H h)
is-equiv-concat-htpy {A = A} {B = B} {f} =
  ind-htpy f
    ( λ g H → (h : (x : A) → B x) → is-equiv (concat-htpy H h))
    ( λ h → is-equiv-id)

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
pr1 (equiv-concat-htpy H h) = concat-htpy H h
pr2 (equiv-concat-htpy H h) = is-equiv-concat-htpy H h
```

#### Concatenating from the right

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h)
  where

  is-section-concat-inv-htpy' :
    ((concat-htpy' f K) ∘ (concat-inv-htpy' f K)) ~ id
  is-section-concat-inv-htpy' L =
    eq-htpy (λ x → is-section-inv-concat' (K x) (L x))

  is-retraction-concat-inv-htpy' :
    ((concat-inv-htpy' f K) ∘ (concat-htpy' f K)) ~ id
  is-retraction-concat-inv-htpy' L =
    eq-htpy (λ x → is-retraction-inv-concat' (K x) (L x))

  is-equiv-concat-htpy' : is-equiv (concat-htpy' f K)
  is-equiv-concat-htpy' =
    is-equiv-is-invertible
      ( concat-inv-htpy' f K)
      ( is-section-concat-inv-htpy')
      ( is-retraction-concat-inv-htpy')

  equiv-concat-htpy' : (f ~ g) ≃ (f ~ h)
  pr1 equiv-concat-htpy' = concat-htpy' f K
  pr2 equiv-concat-htpy' = is-equiv-concat-htpy'
```

### Binary concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h k : (x : A) → B x}
  where

  is-binary-equiv-concat-htpy :
    is-binary-equiv (λ (H : f ~ g) (K : g ~ h) → H ∙h K)
  pr1 is-binary-equiv-concat-htpy K = is-equiv-concat-htpy' f K
  pr2 is-binary-equiv-concat-htpy H = is-equiv-concat-htpy H h

  equiv-binary-concat-htpy :
    (H : f ~ g) (K : h ~ k) → (g ~ h) ≃ (f ~ k)
  equiv-binary-concat-htpy H K = equiv-concat-htpy' f K ∘e equiv-concat-htpy H h
```

### Horizontal composition of homotopies

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  where

  horizontal-concat-htpy² :
    { H H' : f ~ g} → H ~ H' →
    { K K' : g ~ h} → K ~ K' →
    ( H ∙h K) ~ (H' ∙h K')
  horizontal-concat-htpy² α β x = horizontal-concat-Id² (α x) (β x)
```

### Unit laws for horizontal concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  {H H' : f ~ g}
  where

  compute-right-refl-htpy-horizontal-concat-htpy² :
    (α : H ~ H') (K : g ~ h) →
    horizontal-concat-htpy² α refl-htpy ~ right-whisker-concat-htpy α K
  compute-right-refl-htpy-horizontal-concat-htpy² α K x =
    compute-right-refl-horizontal-concat-Id² (α x)

  compute-left-refl-htpy-horizontal-concat-htpy² :
    (K : h ~ f) (α : H ~ H') →
    horizontal-concat-htpy² refl-htpy α ~ left-whisker-concat-htpy K α
  compute-left-refl-htpy-horizontal-concat-htpy² K α x =
    compute-left-refl-horizontal-concat-Id² (α x)
```

### Vertical inverses distribute over horizontal concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  {H H' : f ~ g} {K K' : g ~ h}
  where

  distributive-inv-horizontal-concat-htpy² :
    (α : H ~ H') (β : K ~ K) →
    inv-htpy (horizontal-concat-htpy² α β) ~
    horizontal-concat-htpy² (inv-htpy α) (inv-htpy β)
  distributive-inv-horizontal-concat-htpy² α β x =
    distributive-inv-horizontal-concat-Id² (α x) (β x)
```

### The interchange law for horizontal composition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  {H H' H'' : f ~ g} (α : H ~ H') (α' : H' ~ H'') {K K' K'' : g ~ h}
  (β : K ~ K') (β' : K' ~ K'')
  where

  interchange-htpy² :
    horizontal-concat-htpy² (α ∙h α') (β ∙h β') ~
    (horizontal-concat-htpy² α β) ∙h (horizontal-concat-htpy² α' β')
  interchange-htpy² x = interchange-Id² (α x) (α' x) (β x) (β' x)
```

### Three dimensional concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  where

  z-concat-htpy³ :
    {H K : f ~ g} {L M : g ~ h} {α β : H ~ K} {δ ε : L ~ M}
    (γ : α ~ β) (η : δ ~ ε) →
    horizontal-concat-htpy² α δ ~ horizontal-concat-htpy² β ε
  z-concat-htpy³ γ η x = z-concat-Id³ (γ x) (η x)
```

### Transposing homotopies is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h)
  where

  is-equiv-left-transpose-htpy-concat :
    is-equiv (left-transpose-htpy-concat H K L)
  is-equiv-left-transpose-htpy-concat =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-left-transpose-eq-concat (H x) (K x) (L x))

  equiv-left-transpose-htpy-concat : (H ∙h K ~ L) ≃ (K ~ inv-htpy H ∙h L)
  pr1 equiv-left-transpose-htpy-concat = left-transpose-htpy-concat H K L
  pr2 equiv-left-transpose-htpy-concat = is-equiv-left-transpose-htpy-concat

  is-equiv-right-transpose-htpy-concat :
    is-equiv (right-transpose-htpy-concat H K L)
  is-equiv-right-transpose-htpy-concat =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-right-transpose-eq-concat (H x) (K x) (L x))

  equiv-right-transpose-htpy-concat : (H ∙h K ~ L) ≃ (H ~ L ∙h inv-htpy K)
  pr1 equiv-right-transpose-htpy-concat = right-transpose-htpy-concat H K L
  pr2 equiv-right-transpose-htpy-concat = is-equiv-right-transpose-htpy-concat

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ h) (K : f ~ g) (L : g ~ h)
  where

  equiv-left-transpose-htpy-concat' : (H ~ K ∙h L) ≃ (inv-htpy K ∙h H ~ L)
  equiv-left-transpose-htpy-concat' =
    ( equiv-inv-htpy L ((inv-htpy K) ∙h H)) ∘e
    ( equiv-left-transpose-htpy-concat K L H) ∘e
    ( equiv-inv-htpy H (K ∙h L))

  equiv-right-transpose-htpy-concat' : (H ~ K ∙h L) ≃ (H ∙h inv-htpy L ~ K)
  equiv-right-transpose-htpy-concat' =
    ( equiv-inv-htpy K (H ∙h (inv-htpy L))) ∘e
    ( equiv-right-transpose-htpy-concat K L H) ∘e
    ( equiv-inv-htpy H (K ∙h L))
```

### Computing dependent-identifications in the type family `eq-value` of dependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  is-equiv-map-compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    is-equiv (map-compute-dependent-identification-eq-value f g p q r)
  is-equiv-map-compute-dependent-identification-eq-value refl q r =
    is-equiv-comp
      ( inv)
      ( concat' r (right-unit ∙ ap-id q))
      ( is-equiv-concat' r (right-unit ∙ ap-id q))
      ( is-equiv-inv r q)

  compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    coherence-square-identifications (ap (tr B p) q) (apd f p) (apd g p) r ≃
    dependent-identification (eq-value f g) p q r
  pr1 (compute-dependent-identification-eq-value p q r) =
    map-compute-dependent-identification-eq-value f g p q r
  pr2 (compute-dependent-identification-eq-value p q r) =
    is-equiv-map-compute-dependent-identification-eq-value p q r

  map-inv-compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    dependent-identification (eq-value f g) p q r →
    coherence-square-identifications (ap (tr B p) q) (apd f p) (apd g p) r
  map-inv-compute-dependent-identification-eq-value p q r =
    map-inv-equiv (compute-dependent-identification-eq-value p q r)
```

### Computing dependent-identifications in the type family `eq-value` of ordinary functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  is-equiv-map-compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    is-equiv (map-compute-dependent-identification-eq-value-function f g p q r)
  is-equiv-map-compute-dependent-identification-eq-value-function refl q r =
    is-equiv-comp
      ( inv)
      ( concat' r right-unit)
      ( is-equiv-concat' r right-unit)
      ( is-equiv-inv r q)

  compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y) →
    coherence-square-identifications q (ap f p) (ap g p) r ≃
    dependent-identification (eq-value f g) p q r
  pr1 (compute-dependent-identification-eq-value-function p q r) =
    map-compute-dependent-identification-eq-value-function f g p q r
  pr2 (compute-dependent-identification-eq-value-function p q r) =
    is-equiv-map-compute-dependent-identification-eq-value-function p q r

  map-inv-compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y) →
    dependent-identification (eq-value f g) p q r →
    coherence-square-identifications q (ap f p) (ap g p) r
  map-inv-compute-dependent-identification-eq-value-function p q r =
    map-inv-equiv (compute-dependent-identification-eq-value-function p q r)
```

### Relation between between `compute-dependent-identification-eq-value-function` and `nat-htpy`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {B : UU l2} (f g : A → B)
  (H : f ~ g)
  where

  nat-htpy-apd-htpy :
    (p : a0 ＝ a1) →
    (map-inv-equiv (compute-dependent-identification-eq-value-function
      f g p (H a0) (H a1))) (apd H p) ＝ inv (nat-htpy H p)
  nat-htpy-apd-htpy refl =
    inv
      ( ap
        ( map-inv-equiv
          ( compute-dependent-identification-eq-value-function f g refl
            ( H a0)
            ( H a0)))
        ( ap inv (left-inv right-unit))) ∙
      ( is-retraction-map-inv-equiv
        ( compute-dependent-identification-eq-value-function f g refl
          ( H a0)
          ( H a1))
        ( inv right-unit))
```

### Action on identifications at `eq-htpy`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  {h k : (x : A) → B x}
  where

  compute-eq-htpy-ap :
    (p : h ~ k) →
    eq-htpy (λ i → ap (f i) (p i)) ＝ ap (map-Π f) (eq-htpy p)
  compute-eq-htpy-ap =
    ind-htpy
      ( h)
      ( λ k p → eq-htpy (λ i → ap (f i) (p i)) ＝ ap (map-Π f) (eq-htpy p))
      ( eq-htpy-refl-htpy (map-Π f h) ∙
        inv (ap² (map-Π f) (eq-htpy-refl-htpy h)))
```

## See also

- [Multivariable homotopies](foundation.multivariable-homotopies.md).
- The [whiskering operations](foundation.whiskering-homotopies-composition.md)
  on homotopies.
