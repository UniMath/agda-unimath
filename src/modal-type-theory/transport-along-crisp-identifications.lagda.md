# Transport along crisp identifications

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.transport-along-crisp-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
```

</details>

## Idea

Given a [crisp](modal-type-theory.crisp-types.md) type family `B` that is
[defined on crisp elements](modal-type-theory.crisp-function-types.md) of `A`, a
crisp [identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`
and a crisp element `b : B x`, we can
{{#concept "transport" Disambiguation="along crisp identifications" Agda=crisp-tr}}
the element `b` along the crisp identification `p` to obtain an element
`crisp-tr B p b : B y`.

This is a strengthening of
[transport along identifications](foundation.transport-along-identifications.md)
for crisp identifications, because the type family `B` is allowed to depend only
crisply on the base type `A`.

## Definitions

### Transport along crisp identifications

```agda
crisp-tr :
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  (@♭ B : @♭ A → UU l2) {@♭ x y : A}
  (@♭ p : x ＝ y) → @♭ B x → B y
crisp-tr B refl x = x
```

## Properties

### Transport preserves concatenation of crisp identifications

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  crisp-tr-concat :
    {@♭ x y z : A} (@♭ p : x ＝ y) (@♭ q : y ＝ z) (@♭ b : B x) →
    crisp-tr B (p ∙ q) b ＝ crisp-tr B q (crisp-tr B p b)
  crisp-tr-concat p q b =
    crisp-based-ind-Id
      ( λ y q → crisp-tr B (p ∙ q) b ＝ crisp-tr B q (crisp-tr B p b))
      ( crisp-based-ind-Id
        ( λ y p → crisp-tr B (p ∙ refl) b ＝ crisp-tr B p b)
        ( refl)
        ( p))
      ( q)
```

### Transposing crisp transport along the inverse of a crisp identification

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  eq-transpose-crisp-tr :
    {@♭ x y : A} (@♭ p : x ＝ y) {@♭ u : B x} {@♭ v : B y} →
    @♭ v ＝ crisp-tr B p u → crisp-tr B (inv p) v ＝ u
  eq-transpose-crisp-tr p {u} {.(crisp-tr B p u)} refl =
    crisp-based-ind-Id (λ y p → crisp-tr B (inv p) (crisp-tr B p u) ＝ u) refl p

  eq-transpose-crisp-tr' :
    {@♭ x y : A} (@♭ p : x ＝ y) {@♭ u : B x} {@♭ v : B y} →
    @♭ crisp-tr B p u ＝ v → u ＝ crisp-tr B (inv p) v
  eq-transpose-crisp-tr' p {u} {.(crisp-tr B p u)} refl =
    crisp-based-ind-Id (λ y p → u ＝ crisp-tr B (inv p) (crisp-tr B p u)) refl p
```

### Every crisp family of maps preserves crisp transport

```agda
preserves-crisp-tr :
  {@♭ l1 l2 l3 : Level} {@♭ I : UU l1}
  {@♭ A : @♭ I → UU l2} {@♭ B : @♭ I → UU l3}
  (@♭ f : (@♭ i : I) → A i → B i)
  {@♭ i j : I} (@♭ p : i ＝ j) (@♭ x : A i) →
  f j (crisp-tr A p x) ＝ crisp-tr B p (f i x)
preserves-crisp-tr {A = A} {B} f {i} p x =
  crisp-based-ind-Id
    ( λ j p → f j (crisp-tr A p x) ＝ crisp-tr B p (f i x))
    ( refl)
    ( p)
```

### Transporting along the action on crisp identifications of a function

```agda
crisp-tr-ap :
  {@♭ l1 l2 l3 l4 : Level}
  {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} {@♭ C : UU l3} {@♭ D : @♭ C → UU l4}
  (@♭ f : A → C) (@♭ g : (@♭ x : A) → B x → D (f x))
  {@♭ x y : A} (@♭ p : x ＝ y) (@♭ z : B x) →
  crisp-tr D (ap f p) (g x z) ＝ g y (crisp-tr B p z)
crisp-tr-ap {A = A} {B} {C} {D} f g {x} p z =
  crisp-based-ind-Id
    ( λ y p → crisp-tr D (ap f p) (g x z) ＝ g y (crisp-tr B p z))
    ( refl)
    ( p)
```

### Computing maps out of crisp identity types as crisp transports

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} {@♭ a : A}
  (@♭ f : (@♭ x : A) → @♭ (a ＝ x) → B x)
  where

  compute-map-out-of-crisp-identity-type :
    (@♭ x : A) (@♭ p : a ＝ x) → f x p ＝ crisp-tr B p (f a refl)
  compute-map-out-of-crisp-identity-type x p =
    crisp-based-ind-Id (λ x p → f x p ＝ crisp-tr B p (f a refl)) refl p
```

### Computing crisp transport in the crisp type family of crisp identifications with a fixed target

```agda
crisp-tr-Id-left :
  {@♭ l : Level} {@♭ A : UU l} {@♭ a b c : A} (@♭ q : b ＝ c) (@♭ p : b ＝ a) →
  crisp-tr (_＝ a) q p ＝ (inv q ∙ p)
crisp-tr-Id-left {a = a} q p =
  crisp-based-ind-Id (λ y q → crisp-tr (_＝ a) q p ＝ (inv q ∙ p)) refl q
```

### Computing crisp transport in the crisp type family of crisp identifications with a fixed source

```agda
crisp-tr-Id-right :
  {@♭ l : Level} {@♭ A : UU l} {@♭ a b c : A} (@♭ q : b ＝ c) (@♭ p : a ＝ b) →
  crisp-tr (a ＝_) q p ＝ (p ∙ q)
crisp-tr-Id-right {a = a} q p =
  crisp-based-ind-Id (λ y q → crisp-tr (a ＝_) q p ＝ (p ∙ q)) (inv right-unit) q
```

### Substitution law for crisp transport

```agda
substitution-law-crisp-tr :
  {@♭ l1 l2 l3 : Level} {@♭ X : UU l1} {@♭ A : UU l2} (@♭ B : @♭ A → UU l3)
  (@♭ f : X → A)
  {@♭ x y : X} (@♭ p : x ＝ y) {@♭ x' : B (f x)} →
  crisp-tr B (ap f p) x' ＝ crisp-tr (λ (@♭ x : X) → B (f x)) p x'
substitution-law-crisp-tr {X = X} B f p {x'} =
  crisp-based-ind-Id
    ( λ y p → crisp-tr B (ap f p) x' ＝ crisp-tr (λ (@♭ x : X) → B (f x)) p x')
    ( refl)
    ( p)
```
