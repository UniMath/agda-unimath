# Function extensionality

```agda
module foundation.function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.function-extensionality public

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

</details>

## Idea

The function extensionality axiom asserts that identifications of (dependent) functions are equivalently described as pointwise equalities between them. In other words, a function is completely determined by its values.

In this file we postulate the function extensionality axiom. Its statement is defined in [`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).

## Postulate

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  postulate funext : (f : (x : A) → B x) → FUNEXT f

  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext {f = f} {g}) = htpy-eq
  pr2 (equiv-funext {f = f} {g}) = funext f g

  abstract
    eq-htpy : {f g : (x : A) → B x} → (f ~ g) → f ＝ g
    eq-htpy = map-inv-is-equiv (funext _ _)

    issec-eq-htpy :
      {f g : (x : A) → B x} → (htpy-eq ∘ (eq-htpy {f = f} {g = g})) ~ id
    issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)

    isretr-eq-htpy :
      {f g : (x : A) → B x} → (eq-htpy ∘ (htpy-eq {f = f} {g = g})) ~ id
    isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

    is-equiv-eq-htpy :
      (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
    is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

    eq-htpy-refl-htpy :
      (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
    eq-htpy-refl-htpy f = isretr-eq-htpy refl

  equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
  pr1 (equiv-eq-htpy {f = f} {g}) = eq-htpy
  pr2 (equiv-eq-htpy {f = f} {g}) = is-equiv-eq-htpy f g
```

## See also

- That the univalence axiom implies function extensionality is proven in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
