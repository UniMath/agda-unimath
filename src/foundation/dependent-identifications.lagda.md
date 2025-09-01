# Dependent identifications

```agda
module foundation.dependent-identifications where

open import foundation-core.dependent-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.transport-along-higher-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

We characterize dependent paths in the family of dependent paths; define the
groupoidal operators on dependent paths; define the coherence paths; prove the
operators are equivalences.

## Properties

### Computing twice iterated dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  map-compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    p' ＝ tr² B α x' ∙ q' → dependent-identification² B α p' q'
  map-compute-dependent-identification² refl q p' q' = q'

  map-inv-compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    dependent-identification² B α p' q' → p' ＝ tr² B α x' ∙ q'
  map-inv-compute-dependent-identification² refl q p' q' = q'

  is-section-map-inv-compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    ( map-compute-dependent-identification² α p' q' ∘
      map-inv-compute-dependent-identification² α p' q') ~ id
  is-section-map-inv-compute-dependent-identification² refl q p' q' = refl

  is-retraction-map-inv-compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    ( map-inv-compute-dependent-identification² α p' q' ∘
      map-compute-dependent-identification² α p' q') ~ id
  is-retraction-map-inv-compute-dependent-identification² refl q p' q' = refl

  is-equiv-map-compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    is-equiv (map-compute-dependent-identification² α p' q')
  is-equiv-map-compute-dependent-identification² α p' q' =
    is-equiv-is-invertible
      ( map-inv-compute-dependent-identification² α p' q')
      ( is-section-map-inv-compute-dependent-identification² α p' q')
      ( is-retraction-map-inv-compute-dependent-identification² α p' q')

  compute-dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    (p' ＝ tr² B α x' ∙ q') ≃ dependent-identification² B α p' q'
  pr1 (compute-dependent-identification² α p' q') =
    map-compute-dependent-identification² α p' q'
  pr2 (compute-dependent-identification² α p' q') =
    is-equiv-map-compute-dependent-identification² α p' q'
```

### The groupoidal structure of dependent identifications

We show that there is a dependent groupoidal structure on the dependent
identifications. The statement of the groupoid laws use dependent
identifications, due to the dependent nature of dependent identifications.

#### Concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  concat-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z} →
    dependent-identification B p x' y' →
    dependent-identification B q y' z' →
    dependent-identification B (p ∙ q) x' z'
  concat-dependent-identification refl q p' q' = ap (tr B q) p' ∙ q'

  compute-concat-dependent-identification-left-base-refl :
    { y z : A} (q : y ＝ z) →
    { x' y' : B y} {z' : B z} (p' : x' ＝ y') →
    ( q' : dependent-identification B q y' z') →
    concat-dependent-identification refl q p' q' ＝ ap (tr B q) p' ∙ q'
  compute-concat-dependent-identification-left-base-refl q p' q' = refl

  compute-concat-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    {x' : B x} {y' : B y} {z' : B z} →
    (p' : dependent-identification B p x' y') →
    (q' : dependent-identification B q y' z') →
    concat-dependent-identification p q p' q' ＝ tr-concat p q x' ∙ ap (tr B q) p' ∙ q'
  compute-concat-dependent-identification refl q p' q' = refl
```

#### Strictly right unital concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  right-strict-concat-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z} →
    dependent-identification B p x' y' →
    dependent-identification B q y' z' →
    dependent-identification B (p ∙ᵣ q) x' z'
  right-strict-concat-dependent-identification p refl p' q' = p' ∙ᵣ q'

  compute-right-strict-concat-dependent-identification-right-base-refl :
    { x y : A} (p : x ＝ y) →
    { x' : B x} {y' z' : B y} (p' : dependent-identification B p x' y') →
    ( q' : y' ＝ z') →
    right-strict-concat-dependent-identification p refl p' q' ＝ p' ∙ᵣ q'
  compute-right-strict-concat-dependent-identification-right-base-refl q p' q' =
    refl
```

#### Inverses of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  inv-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y} →
    dependent-identification B p x' y' →
    dependent-identification B (inv p) y' x'
  inv-dependent-identification refl = inv
```

#### Associativity of concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  assoc-dependent-identification :
    {x y z u : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ u)
    {x' : B x} {y' : B y} {z' : B z} {u' : B u}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q y' z')
    (r' : dependent-identification B r z' u') →
    dependent-identification² B
      ( assoc p q r)
      ( concat-dependent-identification B
        ( p ∙ q)
        ( r)
        ( concat-dependent-identification B p q p' q')
        ( r'))
      ( concat-dependent-identification B
        ( p)
        ( q ∙ r)
        ( p')
        ( concat-dependent-identification B q r q' r'))
  assoc-dependent-identification refl q r refl q' r' = refl
```

### Unit laws for concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  right-unit-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : dependent-identification B p x' y') →
    dependent-identification²
      ( B)
      ( right-unit {p = p})
      ( concat-dependent-identification B p refl q refl)
      ( q)
  right-unit-dependent-identification refl refl = refl

  left-unit-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : dependent-identification B p x' y') →
    dependent-identification²
      ( B)
      ( left-unit {p = p})
      ( concat-dependent-identification B refl p
        ( refl-dependent-identification B)
        ( q))
      ( q)
  left-unit-dependent-identification p q = refl
```

### Inverse laws for dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  right-inv-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : dependent-identification B p x' y') →
    dependent-identification² B
      ( right-inv p)
      ( concat-dependent-identification B
        ( p)
        ( inv p)
        ( q)
        ( inv-dependent-identification B p q))
      ( refl-dependent-identification B)
  right-inv-dependent-identification refl refl = refl

  left-inv-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : dependent-identification B p x' y') →
    dependent-identification²
      ( B)
      ( left-inv p)
      ( concat-dependent-identification B
        ( inv p)
        ( p)
        ( inv-dependent-identification B p q)
        ( q))
      ( refl-dependent-identification B)
  left-inv-dependent-identification refl refl = refl
```

### The inverse of dependent identifications is involutive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  inv-inv-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : dependent-identification B p x' y') →
    dependent-identification² B
      ( inv-inv p)
      ( inv-dependent-identification B
        ( inv p)
        ( inv-dependent-identification B p q))
      ( q)
  inv-inv-dependent-identification refl = inv-inv
```

### The inverse distributes over concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  distributive-inv-concat-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q y' z') →
    dependent-identification² B
      ( distributive-inv-concat p q)
      ( inv-dependent-identification B
        ( p ∙ q)
        ( concat-dependent-identification B p q p' q'))
      ( concat-dependent-identification B
        ( inv q)
        ( inv p)
        ( inv-dependent-identification B q q')
        ( inv-dependent-identification B p p'))
  distributive-inv-concat-dependent-identification refl refl refl refl = refl
```

## See also

- [Binary dependent identifications](foundation.binary-dependent-identifications.md)
