# Binary transport

```agda
module foundation.binary-transport where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given a binary relation `B : A → A → UU` and identifications `p : x ＝ x'` and `q : y ＝ y'` in `A`, the binary transport of `B` is an operation

```md
  binary-tr B p q : B x y → B x' y'
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  where

  binary-tr :
    {x x' : A} {y y' : B} (p : x ＝ x') (q : y ＝ y') → C x y → C x' y'
  binary-tr refl refl = id

  is-equiv-binary-tr :
    {x x' : A} {y y' : B} (p : x ＝ x') (q : y ＝ y') → is-equiv (binary-tr p q)
  is-equiv-binary-tr refl refl = is-equiv-id

  equiv-binary-tr :
    {x x' : A} {y y' : B} (p : x ＝ x') (q : y ＝ y') → C x y ≃ C x' y'
  pr1 (equiv-binary-tr p q) = binary-tr p q
  pr2 (equiv-binary-tr p q) = is-equiv-binary-tr p q
```
