# Equality of dependent pair types

```agda
module foundation.equality-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.equality-dependent-pair-types public

open import foundation.identity-types

open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

</details>

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  comp-eq-pair-Σ :
    {x y z : A} (a : B x) (b : B y) (c : B z) (p : x ＝ y) (q : y ＝ z) →
    ( r : tr B p a ＝ b) (s : tr B q b ＝ c) →
    ( concat
      {x = pair x a}
      {y = pair y b}
      ( eq-pair-Σ p r)
      ( pair z c)
      ( eq-pair-Σ q s)) ＝
    ( eq-pair-Σ (p ∙ q) (tr-concat {B = B} p q a ∙ (ap (tr B q) r ∙ s)))
  comp-eq-pair-Σ a .a .a refl refl refl refl = refl

  comp-pair-eq-Σ : {s t u : Σ A B} (p : s ＝ t) (q : t ＝ u) →
    (pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q)) ＝ pr1 (pair-eq-Σ (p ∙ q))
  comp-pair-eq-Σ refl refl = refl

  ap-pair-eq-Σ : {l3 : Level} (X : UU l3) (f : X → Σ A B)
    (x y : X) (p : x ＝ y) →
    (pr1 (pair-eq-Σ (ap f p))) ＝ (ap (λ x → pr1 (f x)) p)
  ap-pair-eq-Σ X f x .x refl = refl

  inv-eq-pair-Σ :
    {x y : A} (a : B x) (b : B y) (p : x ＝ y) (r : tr B p a ＝ b) →
    ( inv (eq-pair-Σ p r)) ＝
    ( eq-pair-Σ
      ( inv p)
      ( tr
        ( λ x → tr B (inv p) b ＝ x)
        ( isretr-inv-tr B p a)
        ( ap (tr B (inv p)) (inv r))))
  inv-eq-pair-Σ a .a refl refl = refl
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-equality-fibers-of-maps.md).
