# Equality of dependent pair types

```agda
module foundation.equality-dependent-pair-types where

open import foundation-core.equality-dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
```

</details>

## Idea

The operation [`eq-pair-Σ`](foundation-core.equality-dependent-pair-types.md)
can be seen as a "vertical composition" operation that combines an
[identification](foundation-core.identity-types.md) and a
[dependent identification](foundation.dependent-identifications.md) over it into
a single identification. This operation preserves, in the appropriate sense, the
groupoidal structure on dependent identifications.

## Properties

### Interchange law of concatenation and `eq-pair-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  interchange-concat-eq-pair-Σ :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z} →
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q y' z') →
    eq-pair-Σ (p ∙ q) (concat-dependent-identification B p q p' q') ＝
    ( eq-pair-Σ p p' ∙ eq-pair-Σ q q')
  interchange-concat-eq-pair-Σ refl q refl q' = refl
```

### Interchange law for concatenation and `pair-eq-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  interchange-concat-pair-eq-Σ :
    {x y z : Σ A B} (p : x ＝ y) (q : y ＝ z) →
    pair-eq-Σ (p ∙ q) ＝
    ( pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q) ,
      concat-dependent-identification B
        ( pr1 (pair-eq-Σ p))
        ( pr1 (pair-eq-Σ q))
        ( pr2 (pair-eq-Σ p))
        ( pr2 (pair-eq-Σ q)))
  interchange-concat-pair-eq-Σ refl q = refl

  pr1-interchange-concat-pair-eq-Σ :
    {x y z : Σ A B} (p : x ＝ y) (q : y ＝ z) →
    pr1 (pair-eq-Σ (p ∙ q)) ＝ (pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q))
  pr1-interchange-concat-pair-eq-Σ p q =
    ap pr1 (interchange-concat-pair-eq-Σ p q)
```

### Distributivity of `inv` over `eq-pair-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  distributive-inv-eq-pair-Σ :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y') →
    inv (eq-pair-Σ p p') ＝
    eq-pair-Σ (inv p) (inv-dependent-identification B p p')
  distributive-inv-eq-pair-Σ refl refl = refl

  distributive-inv-eq-pair-Σ-refl :
    {x : A} {x' y' : B x} (p' : x' ＝ y') →
    inv (eq-pair-eq-fiber p') ＝ eq-pair-Σ {A = A} {B = B} refl (inv p')
  distributive-inv-eq-pair-Σ-refl refl = refl
```

### Computing `pair-eq-Σ` at an identification of the form `ap f p`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : A → UU l3} (f : X → Σ A B)
  where

  pair-eq-Σ-ap :
    {x y : X} (p : x ＝ y) →
    pair-eq-Σ (ap f p) ＝
    ( ( ap (pr1 ∘ f) p) ,
      ( substitution-law-tr B (pr1 ∘ f) p ∙ apd (pr2 ∘ f) p))
  pair-eq-Σ-ap refl = refl

  pr1-pair-eq-Σ-ap :
    {x y : X} (p : x ＝ y) →
    pr1 (pair-eq-Σ (ap f p)) ＝ ap (pr1 ∘ f) p
  pr1-pair-eq-Σ-ap refl = refl
```

### Computing action of functions on identifications of the form `eq-pair-Σ p q`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {Y : UU l3} (f : Σ A B → Y)
  where

  compute-ap-eq-pair-Σ :
    { x y : A} (p : x ＝ y) {b : B x} {b' : B y} →
    ( q : dependent-identification B p b b') →
    ap f (eq-pair-Σ p q) ＝ (ap f (eq-pair-Σ p refl) ∙ ap (ev-pair f y) q)
  compute-ap-eq-pair-Σ refl refl = refl
```

### Equality of dependent pair types consists of two orthogonal components

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  triangle-eq-pair-Σ :
    { a a' : A} (p : a ＝ a') →
    { b : B a} {b' : B a'} (q : dependent-identification B p b b') →
    eq-pair-Σ p q ＝ (eq-pair-Σ p refl ∙ eq-pair-Σ refl q)
  triangle-eq-pair-Σ refl q = refl
```

### Computing identifications in iterated dependent pair types

#### Computing identifications in dependent pair types of the form Σ (Σ A B) C

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3}
  where

  Eq-Σ²' : (s t : Σ (Σ A B) C) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-Σ²' s t =
    Σ ( Eq-Σ (pr1 s) (pr1 t))
      ( λ q → dependent-identification C (eq-pair-Σ' q) (pr2 s) (pr2 t))

  equiv-triple-eq-Σ' :
    (s t : Σ (Σ A B) C) →
    (s ＝ t) ≃ Eq-Σ²' s t
  equiv-triple-eq-Σ' s t =
    ( equiv-Σ
      ( λ q →
        ( dependent-identification
          ( C)
          ( eq-pair-Σ' q)
          ( pr2 s)
          ( pr2 t)))
      ( equiv-pair-eq-Σ (pr1 s) (pr1 t))
      ( λ p →
        ( equiv-tr
          ( λ q → dependent-identification C q (pr2 s) (pr2 t))
          ( inv (is-section-pair-eq-Σ (pr1 s) (pr1 t) p))))) ∘e
    ( equiv-pair-eq-Σ s t)

  triple-eq-Σ' :
    (s t : Σ (Σ A B) C) →
    (s ＝ t) → Eq-Σ²' s t
  triple-eq-Σ' s t = map-equiv (equiv-triple-eq-Σ' s t)
```

#### Computing dependent identifications on the second component

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  coh-eq-base-Σ² :
    {s t : Σ A (λ x → Σ (B x) λ y → C x y)} (p : s ＝ t) →
    eq-base-eq-pair p ＝
    eq-base-eq-pair (eq-base-eq-pair (ap (map-inv-associative-Σ' A B C) p))
  coh-eq-base-Σ² refl = refl

  dependent-eq-second-component-eq-Σ² :
    {s t : Σ A (λ x → Σ (B x) λ y → C x y)} (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair p) (pr1 (pr2 s)) (pr1 (pr2 t))
  dependent-eq-second-component-eq-Σ² {s = s} {t = t} p =
    ( ap (λ q → tr B q (pr1 (pr2 s))) (coh-eq-base-Σ² p)) ∙
    ( pr2
      ( pr1
        ( triple-eq-Σ'
          ( map-inv-associative-Σ' A B C s)
          ( map-inv-associative-Σ' A B C t)
          ( ap (map-inv-associative-Σ' A B C) p))))
```

#### Computing dependent identifications on the third component

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (D : (x : A) → B x → C x → UU l4)
  where

  coh-eq-base-Σ³ :
    { s t : Σ A (λ x → Σ (B x) (λ y → Σ (C x) (D x y)))} (p : s ＝ t) →
    eq-base-eq-pair p ＝
    eq-base-eq-pair (ap (map-equiv (interchange-Σ-Σ-Σ D)) p)
  coh-eq-base-Σ³ refl = refl

  dependent-eq-third-component-eq-Σ³ :
    { s t : Σ A (λ x → Σ (B x) (λ y → Σ (C x) (D x y)))} (p : s ＝ t) →
    dependent-identification C
      ( eq-base-eq-pair p)
      ( pr1 (pr2 (pr2 s)))
      ( pr1 (pr2 (pr2 t)))
  dependent-eq-third-component-eq-Σ³ {s = s} {t = t} p =
    ( ap (λ q → tr C q (pr1 (pr2 (pr2 s)))) (coh-eq-base-Σ³ p)) ∙
    ( dependent-eq-second-component-eq-Σ²
      ( ap (map-equiv (interchange-Σ-Σ-Σ D)) p))
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).
