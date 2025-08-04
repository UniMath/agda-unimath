# Transport along identifications in dependent functions

```agda
module foundation.transport-along-identifications-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Definition

```agda
tr-Π :
  {l1 l2 l3 : Level} {I : UU l1}
  {A : UU l2} {B : I → A → UU l3}
  {i j : I} (p : i ＝ j) →
  (f : (a : A) → B i a) →
  (a : A) →
  tr (λ f → (a : A) → B f a) p f a ＝ tr (λ x → B x a) p (f a)
tr-Π refl f a = refl
```
