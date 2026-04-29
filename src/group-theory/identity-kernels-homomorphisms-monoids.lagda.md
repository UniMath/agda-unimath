# Identity kernels of homomorphisms of monoids

```agda
module group-theory.identity-kernels-homomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Consider a [homomorphism](group-theory.homomorphisms-monoids.md) `f : M → N` between [monoids](group-theory.monoids.md) `M` and `N`. The {{#concept "identity kernel" Disambiguation="homomorphism of monoids" Agda=identity-kernel-hom-Monoid}} of `f` is the [submonoid](group-theory.submonoids.md) `f⁻¹ 1`.

We note that [surjective](foundation.surjective-maps.md) monoid homomorphisms are *not* uniquely identified by their identity kernels. For example, both `id : ℕ → ℕ` and `λ n → min-ℕ 1 n : ℕ → {0,1}` are monoid homomorphisms with trivial identity kernel. Here, the monoid `{0,1}` is the unique [commutative](group-theory.commutative-monoids.md) [idempotent monoid](group-theory.idempotent-monoids.md) with two elements, with `0` being the identity element. The more useful notion of kernel for a homomorphism between monoids is therefore the [congruence relation](group-theory.congruence-relations-monoids.md) given by

```text
  x ∼ y ⇔ (f x ＝ f y)
```
