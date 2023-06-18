# Homotopies

```agda
module foundation.homotopies where

open import foundation-core.homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.sections
open import foundation-core.transport
```

</details>

## Idea

A homotopy of identifications is a pointwise equality between dependent
functions. We defined homotopies in
[`foundation-core.homotopies`](foundation-core.homotopies.md). In this file, we
record some properties of homotopies that require function extensionality,
equivalences, or other.

## Properties

### The total space of homotopies is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  abstract
    is-contr-total-htpy : is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
    is-contr-total-htpy =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (Id f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path f)

  abstract
    is-contr-total-htpy' : is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
    is-contr-total-htpy' =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (λ g → g ＝ f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path' f)
```

### Homotopy induction is equivalent to function extensionality

```agda
ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU (l1 ⊔ l2 ⊔ lsuc l3)
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → f ~ g → UU l3) → section (ev-refl-htpy f C)
```

```agda
abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system f
      ( refl-htpy)
      ( is-contr-total-htpy f)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    ({l : Level} → IND-HTPY {l3 = l} f) → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ g → htpy-eq)
```

### Homotopy induction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    Ind-htpy :
      (f : (x : A) → B x) → IND-HTPY {l3 = l3} f
    Ind-htpy f = IND-HTPY-FUNEXT f (funext f)

    ind-htpy :
      (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
    ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g

    compute-ind-htpy :
      (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      (c : C f refl-htpy) → ind-htpy f C c refl-htpy ＝ c
    compute-ind-htpy f C = pr2 (Ind-htpy f C)
```

### Inverting homotopies is an equivalence

```agda
is-equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
is-equiv-inv-htpy f g =
  is-equiv-has-inverse
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
    eq-htpy (λ x → is-section-inv-concat' (f x) (K x) (L x))

  is-retraction-concat-inv-htpy' :
    ((concat-inv-htpy' f K) ∘ (concat-htpy' f K)) ~ id
  is-retraction-concat-inv-htpy' L =
    eq-htpy (λ x → is-retraction-inv-concat' (f x) (K x) (L x))

  is-equiv-concat-htpy' : is-equiv (concat-htpy' f K)
  is-equiv-concat-htpy' =
    is-equiv-has-inverse
      ( concat-inv-htpy' f K)
      ( is-section-concat-inv-htpy')
      ( is-retraction-concat-inv-htpy')

  equiv-concat-htpy' : (f ~ g) ≃ (f ~ h)
  equiv-concat-htpy' =
    pair (concat-htpy' f K) is-equiv-concat-htpy'
```

### Transposing homotopies is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h)
  where

  is-equiv-inv-con-htpy : is-equiv (inv-con-htpy H K L)
  is-equiv-inv-con-htpy =
    is-equiv-map-Π _ (λ x → is-equiv-inv-con (H x) (K x) (L x))

  equiv-inv-con-htpy : ((H ∙h K) ~ L) ≃ (K ~ ((inv-htpy H) ∙h L))
  equiv-inv-con-htpy = pair (inv-con-htpy H K L) is-equiv-inv-con-htpy

  is-equiv-con-inv-htpy : is-equiv (con-inv-htpy H K L)
  is-equiv-con-inv-htpy =
    is-equiv-map-Π _ (λ x → is-equiv-con-inv (H x) (K x) (L x))

  equiv-con-inv-htpy : ((H ∙h K) ~ L) ≃ (H ~ (L ∙h (inv-htpy K)))
  equiv-con-inv-htpy = pair (con-inv-htpy H K L) is-equiv-con-inv-htpy
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
    (((apd f p) ∙ r) ＝ ((ap (tr B p) q) ∙ (apd g p))) ≃
    (tr (eq-value f g) p q ＝ r)
  pr1 (compute-dependent-identification-eq-value p q r) =
    map-compute-dependent-identification-eq-value f g p q r
  pr2 (compute-dependent-identification-eq-value p q r) =
    is-equiv-map-compute-dependent-identification-eq-value p q r
```

### Computing dependent-identifications in the type family `eq-value` of ordinary functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  is-equiv-map-compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (q' : eq-value f g y) →
    is-equiv (map-compute-dependent-identification-eq-value-function f g p q q')
  is-equiv-map-compute-dependent-identification-eq-value-function refl q q' =
    is-equiv-comp
      ( inv)
      ( concat' q' right-unit)
      ( is-equiv-concat' q' right-unit)
      ( is-equiv-inv q' q)

  compute-dependent-identification-eq-value-function :
    {a0 a1 : A} (p : a0 ＝ a1) (q : f a0 ＝ g a0) (q' : f a1 ＝ g a1) →
    (((ap f p) ∙ q') ＝ (q ∙ (ap g p))) ≃ ((tr (eq-value f g) p q) ＝ q')
  pr1 (compute-dependent-identification-eq-value-function p q q') =
    map-compute-dependent-identification-eq-value-function f g p q q'
  pr2 (compute-dependent-identification-eq-value-function p q q') =
    is-equiv-map-compute-dependent-identification-eq-value-function p q q'
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

## See also

- We postulate that homotopies characterize identifications in (dependent)
  function types in the file
  [`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).
