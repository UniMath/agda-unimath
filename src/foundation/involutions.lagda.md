# Involutions

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.involutions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types funext
open import foundation.equivalence-extensionality funext
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-algebra
open import foundation.homotopy-induction funext
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import structured-types.pointed-types
```

</details>

## Idea

An **involution** on a type `A` is a map `f : A → A` such that `(f ∘ f) ~ id`.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  is-involution : (A → A) → UU l
  is-involution f = (f ∘ f) ~ id

  is-involution-aut : Aut A → UU l
  is-involution-aut e = is-involution (map-equiv e)
```

### The type of involutions on `A`

```agda
involution : {l : Level} → UU l → UU l
involution A = Σ (A → A) is-involution

module _
  {l : Level} {A : UU l} (f : involution A)
  where

  map-involution : A → A
  map-involution = pr1 f

  is-involution-map-involution : is-involution map-involution
  is-involution-map-involution = pr2 f
```

## Properties

### Involutions are equivalences

```agda
is-equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} is-involution-f =
  is-equiv-is-invertible f is-involution-f is-involution-f

is-equiv-map-involution :
  {l : Level} {A : UU l} (f : involution A) → is-equiv (map-involution f)
is-equiv-map-involution = is-equiv-is-involution ∘ is-involution-map-involution

equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → A ≃ A
pr1 (equiv-is-involution {f = f} is-involution-f) = f
pr2 (equiv-is-involution is-involution-f) =
  is-equiv-is-involution is-involution-f

equiv-involution :
  {l : Level} {A : UU l} → involution A → A ≃ A
equiv-involution f =
  equiv-is-involution {f = map-involution f} (is-involution-map-involution f)
```

### Involutions are their own inverse

```agda
htpy-own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → map-inv-equiv f ~ map-equiv f
htpy-own-inverse-is-involution {f = f} is-involution-f x =
  is-injective-equiv f
    ( htpy-eq-equiv (right-inverse-law-equiv f) x ∙
      inv (is-involution-f x))

own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → inv-equiv f ＝ f
own-inverse-is-involution {f = f} =
  eq-htpy-equiv ∘ htpy-own-inverse-is-involution {f = f}
```

### Characterizing equality of involutions

```agda
module _
  {l : Level} {A : UU l}
  where

  coherence-htpy-involution :
    (s t : involution A) → map-involution s ~ map-involution t → UU l
  coherence-htpy-involution s t H =
    ( is-involution-map-involution s) ~
    ( horizontal-concat-htpy H H ∙h is-involution-map-involution t)

  htpy-involution : (s t : involution A) → UU l
  htpy-involution s t =
    Σ ( map-involution s ~ map-involution t)
      ( coherence-htpy-involution s t)

  refl-htpy-involution : (s : involution A) → htpy-involution s s
  pr1 (refl-htpy-involution s) = refl-htpy
  pr2 (refl-htpy-involution s) = refl-htpy

  htpy-eq-involution : (s t : involution A) → s ＝ t → htpy-involution s t
  htpy-eq-involution s .s refl = refl-htpy-involution s

  is-torsorial-htpy-involution :
    (s : involution A) → is-torsorial (htpy-involution s)
  is-torsorial-htpy-involution s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-involution s))
      ( map-involution s , refl-htpy)
      ( is-torsorial-htpy (is-involution-map-involution s))

  is-equiv-htpy-eq-involution :
    (s t : involution A) → is-equiv (htpy-eq-involution s t)
  is-equiv-htpy-eq-involution s =
    fundamental-theorem-id
      ( is-torsorial-htpy-involution s)
      ( htpy-eq-involution s)

  extensionality-involution :
    (s t : involution A) → (s ＝ t) ≃ (htpy-involution s t)
  pr1 (extensionality-involution s t) = htpy-eq-involution s t
  pr2 (extensionality-involution s t) = is-equiv-htpy-eq-involution s t

  eq-htpy-involution : (s t : involution A) → htpy-involution s t → s ＝ t
  eq-htpy-involution s t = map-inv-equiv (extensionality-involution s t)
```

### If `A` is `k`-truncated then the type of involutions is `k`-truncated

```agda
is-trunc-is-involution :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc (succ-𝕋 k) A → (f : A → A) → is-trunc k (is-involution f)
is-trunc-is-involution k is-trunc-A f =
  is-trunc-Π k λ x → is-trunc-A (f (f x)) x

is-involution-Truncated-Type :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc (succ-𝕋 k) A → (A → A) → Truncated-Type l k
pr1 (is-involution-Truncated-Type k is-trunc-A f) = is-involution f
pr2 (is-involution-Truncated-Type k is-trunc-A f) =
  is-trunc-is-involution k is-trunc-A f

is-trunc-involution :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc k A → is-trunc k (involution A)
is-trunc-involution k is-trunc-A =
  is-trunc-Σ
    ( is-trunc-function-type k is-trunc-A)
    ( is-trunc-is-involution k (is-trunc-succ-is-trunc k is-trunc-A))

involution-Truncated-Type :
  {l : Level} (k : 𝕋) → Truncated-Type l k → Truncated-Type l k
pr1 (involution-Truncated-Type k (A , is-trunc-A)) = involution A
pr2 (involution-Truncated-Type k (A , is-trunc-A)) =
  is-trunc-involution k is-trunc-A
```

### Involutions on dependent function types

```agda
involution-Π-involution-fam :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → involution (B x)) → involution ((x : A) → B x)
pr1 (involution-Π-involution-fam i) f x =
  map-involution (i x) (f x)
pr2 (involution-Π-involution-fam i) f =
  eq-htpy (λ x → is-involution-map-involution (i x) (f x))
```

### Coherence of involutions

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : is-involution f)
  where

  coherence-is-involution : UU l
  coherence-is-involution = f ·l H ~ H ·r f
```

## Examples

### The identity function is an involution

```agda
is-involution-id :
  {l : Level} {A : UU l} → is-involution (id {A = A})
is-involution-id = refl-htpy

id-involution :
  {l : Level} {A : UU l} → involution A
pr1 id-involution = id
pr2 id-involution = is-involution-id

involution-Pointed-Type :
  {l : Level} (A : UU l) → Pointed-Type l
pr1 (involution-Pointed-Type A) = involution A
pr2 (involution-Pointed-Type A) = id-involution
```
