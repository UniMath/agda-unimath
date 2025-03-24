# The universal property of dependent pair types

```agda
open import foundation.function-extensionality-axiom

module foundation.universal-property-dependent-pair-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

The {{#concept "universal property of dependent pair types"}} characterizes of
maps out of [dependent pair types](foundation.dependent-pair-types.md). It
states that _uncurried_ maps `(x : Σ A B) → C x` are in correspondence with
_curried_ maps `(a : A) (b : B a) → C (a , b)`.

## Theorem

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3}
  where

  abstract
    is-equiv-ev-pair : is-equiv (ev-pair {C = C})
    pr1 (pr1 is-equiv-ev-pair) = ind-Σ
    pr2 (pr1 is-equiv-ev-pair) = refl-htpy
    pr1 (pr2 is-equiv-ev-pair) = ind-Σ
    pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

  abstract
    is-equiv-ind-Σ : is-equiv (ind-Σ {C = C})
    is-equiv-ind-Σ = is-equiv-is-section is-equiv-ev-pair refl-htpy

  equiv-ev-pair : ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (a , b))
  pr1 equiv-ev-pair = ev-pair
  pr2 equiv-ev-pair = is-equiv-ev-pair

  equiv-ind-Σ : ((a : A) (b : B a) → C (a , b)) ≃ ((x : Σ A B) → C x)
  pr1 equiv-ind-Σ = ind-Σ
  pr2 equiv-ind-Σ = is-equiv-ind-Σ
```

## Properties

### Iterated currying

```agda
equiv-ev-pair² :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : A → UU l2} {C : UU l3}
  { X : UU l4} {Y : X → UU l5}
  { Z : ( Σ A B → C) → Σ X Y → UU l6} →
  Σ ( Σ A B → C) (λ k → ( xy : Σ X Y) → Z k xy) ≃
  Σ ( (a : A) → B a → C) (λ k → (x : X) → (y : Y x) → Z (ind-Σ k) (x , y))
equiv-ev-pair² {X = X} {Y = Y} {Z = Z} =
  equiv-Σ
    ( λ k → (x : X) (y : Y x) → Z (ind-Σ k) (x , y))
    ( equiv-ev-pair)
    ( λ k → equiv-ev-pair)

equiv-ev-pair³ :
  { l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level} →
  { A : UU l1} {B : A → UU l2} {C : UU l3}
  { X : UU l4} {Y : X → UU l5} {Z : UU l6}
  { U : UU l7} {V : U → UU l8}
  { W : ((Σ A B) → C) → ((Σ X Y) → Z) → (Σ U V) → UU l9} →
  Σ ( (Σ A B) → C)
    ( λ k →
      Σ ( (Σ X Y) → Z)
        ( λ l → ( uv : Σ U V) → W k l uv)) ≃
  Σ ( (a : A) → B a → C)
    ( λ k →
      Σ ( (x : X) → Y x → Z)
        ( λ l → (u : U) → (v : V u) → W (ind-Σ k) (ind-Σ l) (u , v)))
equiv-ev-pair³ {X = X} {Y = Y} {Z = Z} {U = U} {V = V} {W = W} =
  equiv-Σ
    ( λ k →
      Σ ( (x : X) → Y x → Z)
        ( λ l → (u : U) → (v : V u) → W (ind-Σ k) (ind-Σ l) (u , v)))
    ( equiv-ev-pair)
    ( λ k → equiv-ev-pair²)
```

## See also

- For the universal mapping-into property of dependent pair types, see the
  [type theoretic principle of choice](foundation-core.type-theoretic-principle-of-choice.md)
