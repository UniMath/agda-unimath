# The Eisenstein integers

```agda
module complex-numbers.eisenstein-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "Eisenstein integers" WDID=Q262370 WD="Eisenstein integer" Agda="ℤ[ω]"}}
are the [complex numbers](complex-numbers.complex-numbers.md) of the form
`a + bω`, where `ω = -½ + ½√3i`, and where `a` and `b` are
[integers](elementary-number-theory.integers.md). Note that `ω` is a solution to
the equation `ω² + ω + 1 = 0`.

## Definition

### The underlying type of the Eisenstein integers

```agda
ℤ[ω] : UU lzero
ℤ[ω] = ℤ × ℤ
```

### Observational equality of the Eisenstein integers

```agda
Eq-ℤ[ω] : ℤ[ω] → ℤ[ω] → UU lzero
Eq-ℤ[ω] x y = (pr1 x ＝ pr1 y) × (pr2 x ＝ pr2 y)

refl-Eq-ℤ[ω] : (x : ℤ[ω]) → Eq-ℤ[ω] x x
pr1 (refl-Eq-ℤ[ω] x) = refl
pr2 (refl-Eq-ℤ[ω] x) = refl

Eq-eq-ℤ[ω] : {x y : ℤ[ω]} → x ＝ y → Eq-ℤ[ω] x y
Eq-eq-ℤ[ω] {x} refl = refl-Eq-ℤ[ω] x

eq-Eq-ℤ[ω]' : {x y : ℤ[ω]} → Eq-ℤ[ω] x y → x ＝ y
eq-Eq-ℤ[ω]' {a , b} {.a , .b} (refl , refl) = refl

eq-Eq-ℤ[ω] : {x y : ℤ[ω]} → (pr1 x ＝ pr1 y) → (pr2 x ＝ pr2 y) → x ＝ y
eq-Eq-ℤ[ω] {a , b} {.a , .b} refl refl = refl
```

### The Eisenstein integer zero

```agda
zero-ℤ[ω] : ℤ[ω]
pr1 zero-ℤ[ω] = zero-ℤ
pr2 zero-ℤ[ω] = zero-ℤ
```

### The Eisenstein integer one

```agda
one-ℤ[ω] : ℤ[ω]
pr1 one-ℤ[ω] = one-ℤ
pr2 one-ℤ[ω] = zero-ℤ
```

### The inclusion of the integers into the Eisenstein integers

```agda
eisenstein-int-ℤ : ℤ → ℤ[ω]
pr1 (eisenstein-int-ℤ x) = x
pr2 (eisenstein-int-ℤ x) = zero-ℤ
```

### The Eisenstein integer ω

```agda
ω-ℤ[ω] : ℤ[ω]
pr1 ω-ℤ[ω] = zero-ℤ
pr2 ω-ℤ[ω] = one-ℤ
```

### The Eisenstein integer -ω

```agda
neg-ω-ℤ[ω] : ℤ[ω]
pr1 neg-ω-ℤ[ω] = zero-ℤ
pr2 neg-ω-ℤ[ω] = neg-one-ℤ
```

### Addition of Eisenstein integers

```agda
add-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
pr1 (add-ℤ[ω] (a , b) (a' , b')) = a +ℤ a'
pr2 (add-ℤ[ω] (a , b) (a' , b')) = b +ℤ b'

infixl 35 _+ℤ[ω]_
_+ℤ[ω]_ = add-ℤ[ω]

ap-add-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → x ＝ x' → y ＝ y' → x +ℤ[ω] y ＝ x' +ℤ[ω] y'
ap-add-ℤ[ω] p q = ap-binary add-ℤ[ω] p q
```

### Negatives of Eisenstein integers

```agda
neg-ℤ[ω] : ℤ[ω] → ℤ[ω]
pr1 (neg-ℤ[ω] (a , b)) = neg-ℤ a
pr2 (neg-ℤ[ω] (a , b)) = neg-ℤ b
```

### Multiplication of Eisenstein integers

Note that `(a + bω)(c + dω) = (ac - bd) + (ad + cb - bd)ω`

```agda
mul-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
pr1 (mul-ℤ[ω] (a1 , b1) (a2 , b2)) =
  (a1 *ℤ a2) +ℤ (neg-ℤ (b1 *ℤ b2))
pr2 (mul-ℤ[ω] (a1 , b1) (a2 , b2)) =
  ((a1 *ℤ b2) +ℤ (a2 *ℤ b1)) +ℤ (neg-ℤ (b1 *ℤ b2))

infixl 40 _*ℤ[ω]_
_*ℤ[ω]_ = mul-ℤ[ω]

ap-mul-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → x ＝ x' → y ＝ y' → x *ℤ[ω] y ＝ x' *ℤ[ω] y'
ap-mul-ℤ[ω] p q = ap-binary mul-ℤ[ω] p q
```

### Conjugation of Eisenstein integers

The conjugate of `a + bω` is `a + bω²`, which is `(a - b) - bω`.

```agda
conjugate-ℤ[ω] : ℤ[ω] → ℤ[ω]
pr1 (conjugate-ℤ[ω] (a , b)) = a +ℤ (neg-ℤ b)
pr2 (conjugate-ℤ[ω] (a , b)) = neg-ℤ b

conjugate-conjugate-ℤ[ω] :
  (x : ℤ[ω]) → conjugate-ℤ[ω] (conjugate-ℤ[ω] x) ＝ x
conjugate-conjugate-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω] (is-retraction-right-add-neg-ℤ (neg-ℤ b) a) (neg-neg-ℤ b)
```

### The Eisenstein integers form a ring with conjugation

```agda
left-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → zero-ℤ[ω] +ℤ[ω] x ＝ x
left-unit-law-add-ℤ[ω] (a , b) = eq-Eq-ℤ[ω] refl refl

right-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → x +ℤ[ω] zero-ℤ[ω] ＝ x
right-unit-law-add-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω] (right-unit-law-add-ℤ a) (right-unit-law-add-ℤ b)

associative-add-ℤ[ω] :
  (x y z : ℤ[ω]) → (x +ℤ[ω] y) +ℤ[ω] z ＝ x +ℤ[ω] (y +ℤ[ω] z)
associative-add-ℤ[ω] (a , b) (c , d) (e , f) =
  eq-Eq-ℤ[ω] (associative-add-ℤ a c e) (associative-add-ℤ b d f)

left-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → (neg-ℤ[ω] x) +ℤ[ω] x ＝ zero-ℤ[ω]
left-inverse-law-add-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω] (left-inverse-law-add-ℤ a) (left-inverse-law-add-ℤ b)

right-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → x +ℤ[ω] (neg-ℤ[ω] x) ＝ zero-ℤ[ω]
right-inverse-law-add-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω] (right-inverse-law-add-ℤ a) (right-inverse-law-add-ℤ b)

commutative-add-ℤ[ω] :
  (x y : ℤ[ω]) → x +ℤ[ω] y ＝ y +ℤ[ω] x
commutative-add-ℤ[ω] (a , b) (a' , b') =
  eq-Eq-ℤ[ω] (commutative-add-ℤ a a') (commutative-add-ℤ b b')

left-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → one-ℤ[ω] *ℤ[ω] x ＝ x
left-unit-law-mul-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω]
    ( right-unit-law-add-ℤ a)
    ( ( right-unit-law-add-ℤ (b +ℤ (a *ℤ zero-ℤ))) ∙
      ( ( ap (b +ℤ_) (right-zero-law-mul-ℤ a)) ∙
        ( right-unit-law-add-ℤ b)))

right-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → x *ℤ[ω] one-ℤ[ω] ＝ x
right-unit-law-mul-ℤ[ω] (a , b) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ (right-unit-law-mul-ℤ a) (ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ a))
    ( ( ap-add-ℤ
        ( ap (_+ℤ b) (right-zero-law-mul-ℤ a))
        ( ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ b))

commutative-mul-ℤ[ω] :
  (x y : ℤ[ω]) → x *ℤ[ω] y ＝ y *ℤ[ω] x
commutative-mul-ℤ[ω] (a , b) (c , d) =
  eq-Eq-ℤ[ω]
    ( ap-add-ℤ (commutative-mul-ℤ a c) (ap neg-ℤ (commutative-mul-ℤ b d)))
    ( ap-add-ℤ
      ( commutative-add-ℤ (a *ℤ d) (c *ℤ b))
      ( ap neg-ℤ (commutative-mul-ℤ b d)))

associative-mul-ℤ[ω] :
  (x y z : ℤ[ω]) → (x *ℤ[ω] y) *ℤ[ω] z ＝ x *ℤ[ω] (y *ℤ[ω] z)
associative-mul-ℤ[ω] (a , b) (c , d) (e , f) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( a *ℤ c)
            ( neg-ℤ (b *ℤ d))
            ( e)) ∙
          ( ap-add-ℤ
            ( associative-mul-ℤ a c e)
            ( ( left-negative-law-mul-ℤ (b *ℤ d) e) ∙
              ( ap neg-ℤ (associative-mul-ℤ b d e)))))
        ( ( ap
            ( neg-ℤ)
            ( ( right-distributive-mul-add-ℤ
                ( (a *ℤ d) +ℤ (c *ℤ b))
                ( neg-ℤ (b *ℤ d))
                ( f)) ∙
              ( ap-add-ℤ
                ( ( right-distributive-mul-add-ℤ (a *ℤ d) (c *ℤ b) f) ∙
                  ( ap-add-ℤ
                    ( associative-mul-ℤ a d f)
                    ( ( ap (_*ℤ f) (commutative-mul-ℤ c b)) ∙
                      ( associative-mul-ℤ b c f))))
                ( ( left-negative-law-mul-ℤ (b *ℤ d) f) ∙
                  ( ap neg-ℤ (associative-mul-ℤ b d f)))))) ∙
          ( ( distributive-neg-add-ℤ
              ( (a *ℤ (d *ℤ f)) +ℤ (b *ℤ (c *ℤ f)))
              ( neg-ℤ (b *ℤ (d *ℤ f)))) ∙
            ( ( ap-add-ℤ
                ( distributive-neg-add-ℤ
                  ( a *ℤ (d *ℤ f))
                  ( b *ℤ (c *ℤ f)))
                ( refl
                  { x = neg-ℤ (neg-ℤ (b *ℤ (d *ℤ f)))})) ∙
              ( associative-add-ℤ
                ( neg-ℤ (a *ℤ (d *ℤ f)))
                ( neg-ℤ (b *ℤ (c *ℤ f)))
                ( neg-ℤ (neg-ℤ (b *ℤ (d *ℤ f))))))))) ∙
      ( ( interchange-law-add-add-ℤ
          ( a *ℤ (c *ℤ e))
          ( neg-ℤ (b *ℤ (d *ℤ e)))
          ( neg-ℤ (a *ℤ (d *ℤ f)))
          ( ( neg-ℤ (b *ℤ (c *ℤ f))) +ℤ (neg-ℤ (neg-ℤ (b *ℤ (d *ℤ f)))))) ∙
        ( ap-add-ℤ
          ( ( ap
              ( (a *ℤ (c *ℤ e)) +ℤ_)
              ( inv ( right-negative-law-mul-ℤ a (d *ℤ f)))) ∙
            ( inv
              ( left-distributive-mul-add-ℤ a (c *ℤ e) (neg-ℤ (d *ℤ f)))))
          ( ( ap
              ( (neg-ℤ (b *ℤ (d *ℤ e))) +ℤ_)
              ( inv
                ( distributive-neg-add-ℤ
                  ( b *ℤ (c *ℤ f))
                  ( neg-ℤ (b *ℤ (d *ℤ f)))))) ∙
            ( ( inv
                ( distributive-neg-add-ℤ
                  ( b *ℤ (d *ℤ e))
                  ( (b *ℤ (c *ℤ f)) +ℤ (neg-ℤ (b *ℤ (d *ℤ f)))))) ∙
              ( ap
                ( neg-ℤ)
                ( ( ap
                    ( (b *ℤ (d *ℤ e)) +ℤ_)
                    ( ( ap
                        ( (b *ℤ (c *ℤ f)) +ℤ_)
                        ( inv (right-negative-law-mul-ℤ b (d *ℤ f)))) ∙
                      ( inv
                        ( left-distributive-mul-add-ℤ b
                          ( c *ℤ f)
                          ( neg-ℤ (d *ℤ f)))))) ∙
                  ( ( inv
                      ( left-distributive-mul-add-ℤ b
                        ( d *ℤ e)
                        ( (c *ℤ f) +ℤ (neg-ℤ (d *ℤ f))))) ∙
                    ( ap
                      ( b *ℤ_)
                      ( ( inv
                          ( associative-add-ℤ
                            ( d *ℤ e)
                            ( c *ℤ f)
                            ( neg-ℤ (d *ℤ f)))) ∙
                        ( ap
                          ( _+ℤ (neg-ℤ (d *ℤ f)))
                          ( ( commutative-add-ℤ (d *ℤ e) (c *ℤ f)) ∙
                            ( ap
                              ( (c *ℤ f) +ℤ_)
                              ( commutative-mul-ℤ d e))))))))))))))
    ( ( ap-add-ℤ
        ( ( ap-add-ℤ
            ( ( right-distributive-mul-add-ℤ ac (neg-ℤ bd) f) ∙
              ( ap-add-ℤ
                ( associative-mul-ℤ a c f)
                ( ( left-negative-law-mul-ℤ bd f) ∙
                  ( ( ap neg-ℤ (associative-mul-ℤ b d f)) ∙
                    ( ( inv (right-negative-law-mul-ℤ b df)) ∙
                      ( commutative-mul-ℤ b (neg-ℤ df)))))))
            ( ( left-distributive-mul-add-ℤ e (ad +ℤ cb) (neg-ℤ bd)) ∙
              ( ( ap-add-ℤ
                  ( ( left-distributive-mul-add-ℤ e ad cb) ∙
                    ( ap-add-ℤ
                      ( ( commutative-mul-ℤ e ad) ∙
                        ( ( associative-mul-ℤ a d e) ∙
                          ( ap (a *ℤ_) (commutative-mul-ℤ d e))))
                      ( ( ap (e *ℤ_) (commutative-mul-ℤ c b)) ∙
                        ( ( commutative-mul-ℤ e (b *ℤ c)) ∙
                          ( ( associative-mul-ℤ b c e) ∙
                            ( commutative-mul-ℤ b ce))))))
                  ( ( right-negative-law-mul-ℤ e bd) ∙
                    ( ( ap
                        ( neg-ℤ)
                        ( ( commutative-mul-ℤ e bd) ∙
                          ( associative-mul-ℤ b d e))) ∙
                      ( ap
                        ( neg-ℤ)
                        ( ap (b *ℤ_) (commutative-mul-ℤ d e)))))) ∙
                ( associative-add-ℤ
                  ( a *ℤ ed)
                  ( ce *ℤ b)
                  ( neg-ℤ (b *ℤ ed)))))) ∙
          ( ( interchange-law-add-add-ℤ
              ( a *ℤ cf)
              ( (neg-ℤ df) *ℤ b)
              ( a *ℤ ed)
              ( (ce *ℤ b) +ℤ (neg-ℤ (b *ℤ ed)))) ∙
            ( ( ap-add-ℤ
                ( inv (left-distributive-mul-add-ℤ a cf ed))
                ( ( inv
                    ( associative-add-ℤ
                      ( (neg-ℤ df) *ℤ b)
                      ( ce *ℤ b)
                      ( neg-ℤ (b *ℤ ed)))) ∙
                  ( ap
                    ( _+ℤ (neg-ℤ (b *ℤ ed)))
                    ( ( commutative-add-ℤ ((neg-ℤ df) *ℤ b) (ce *ℤ b)) ∙
                      ( inv
                        ( right-distributive-mul-add-ℤ ce (neg-ℤ df) b)))))) ∙
              ( ( inv
                  ( associative-add-ℤ
                    ( a *ℤ (cf +ℤ ed))
                    ( (ce +ℤ (neg-ℤ df)) *ℤ b)
                    ( neg-ℤ (b *ℤ ed)))) ∙
                ( ( ap
                    ( _+ℤ (neg-ℤ (b *ℤ ed)))
                    ( commutative-add-ℤ
                      ( a *ℤ (cf +ℤ ed))
                      ( (ce +ℤ (neg-ℤ df)) *ℤ b))) ∙
                  ( associative-add-ℤ
                    ( (ce +ℤ (neg-ℤ df)) *ℤ b)
                    ( a *ℤ (cf +ℤ ed))
                    ( neg-ℤ (b *ℤ ed))))))))
        ( ( inv (left-negative-law-mul-ℤ ((ad +ℤ cb) +ℤ (neg-ℤ bd)) f)) ∙
          ( ( ap
              ( _*ℤ f)
              ( ( distributive-neg-add-ℤ (ad +ℤ cb) (neg-ℤ bd)) ∙
                ( ap-add-ℤ (distributive-neg-add-ℤ ad cb) (neg-neg-ℤ bd)))) ∙
            ( ( right-distributive-mul-add-ℤ
                ( (neg-ℤ ad) +ℤ (neg-ℤ cb))
                ( bd)
                ( f)) ∙
              ( ( ap-add-ℤ
                  ( ( right-distributive-mul-add-ℤ (neg-ℤ ad) (neg-ℤ cb) f) ∙
                    ( ap-add-ℤ
                      ( ( left-negative-law-mul-ℤ ad f) ∙
                        ( ( ap
                            ( neg-ℤ)
                            ( associative-mul-ℤ a d f)) ∙
                          ( inv (right-negative-law-mul-ℤ a df))))
                      ( ( left-negative-law-mul-ℤ cb f) ∙
                        ( ap
                          ( neg-ℤ)
                          ( ( ap
                              ( _*ℤ f)
                              ( commutative-mul-ℤ c b)) ∙
                            ( associative-mul-ℤ b c f))))))
                  ( ( associative-mul-ℤ b d f) ∙
                    ( ( inv (neg-neg-ℤ (b *ℤ df))) ∙
                      ( ap neg-ℤ (inv (right-negative-law-mul-ℤ b df)))))) ∙
                ( ( associative-add-ℤ
                    ( a *ℤ ( neg-ℤ df))
                    ( neg-ℤ (b *ℤ cf))
                    ( neg-ℤ (b *ℤ (neg-ℤ df)))) ∙
                  ( ap
                    ( (a *ℤ (neg-ℤ df)) +ℤ_)
                    ( ( inv
                        ( distributive-neg-add-ℤ
                          ( b *ℤ cf)
                          ( b *ℤ (neg-ℤ df)))) ∙
                      ( ap
                        ( neg-ℤ)
                        ( inv
                          ( left-distributive-mul-add-ℤ
                            ( b)
                            ( cf)
                            ( neg-ℤ df)))))))))))) ∙
      ( ( associative-add-ℤ
          ( (ce +ℤ (neg-ℤ df)) *ℤ b)
          ( (a *ℤ (cf +ℤ ed)) +ℤ (neg-ℤ (b *ℤ ed)))
          ( (a *ℤ (neg-ℤ df)) +ℤ (neg-ℤ (b *ℤ (cf +ℤ (neg-ℤ df)))))) ∙
        ( ( ( ap
              ( ((ce +ℤ (neg-ℤ df)) *ℤ b) +ℤ_)
              ( ( interchange-law-add-add-ℤ
                  ( a *ℤ (cf +ℤ ed))
                  ( neg-ℤ (b *ℤ ed))
                  ( a *ℤ (neg-ℤ df))
                  ( neg-ℤ (b *ℤ (cf +ℤ (neg-ℤ df))))) ∙
                ( ap-add-ℤ
                  ( inv
                    ( left-distributive-mul-add-ℤ a (cf +ℤ ed) (neg-ℤ df)))
                  ( ( inv
                      ( distributive-neg-add-ℤ
                        ( b *ℤ ed)
                        ( b *ℤ (cf +ℤ (neg-ℤ df))))) ∙
                    ( ap
                      ( neg-ℤ)
                      ( ( inv
                          ( left-distributive-mul-add-ℤ b ed
                            ( cf +ℤ (neg-ℤ df)))) ∙
                        ( ap
                          ( b *ℤ_)
                          ( ( inv
                              ( associative-add-ℤ ed cf (neg-ℤ df))) ∙
                            ( ap
                              ( _+ℤ (neg-ℤ df))
                              ( commutative-add-ℤ ed cf)))))))))) ∙
            ( inv
              ( associative-add-ℤ
                ( (ce +ℤ (neg-ℤ df)) *ℤ b)
                ( a *ℤ ((cf +ℤ ed) +ℤ (neg-ℤ df)))
                ( neg-ℤ (b *ℤ ((cf +ℤ ed) +ℤ (neg-ℤ df))))))) ∙
          ( ap
            ( _+ℤ (neg-ℤ (b *ℤ ((cf +ℤ ed) +ℤ (neg-ℤ df)))))
            ( commutative-add-ℤ
              ( (ce +ℤ (neg-ℤ df)) *ℤ b)
              ( a *ℤ ((cf +ℤ ed) +ℤ (neg-ℤ df))))))))
    where
    ac = a *ℤ c
    bd = b *ℤ d
    ad = a *ℤ d
    cb = c *ℤ b
    ce = c *ℤ e
    cf = c *ℤ f
    ed = e *ℤ d
    df = d *ℤ f

left-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  x *ℤ[ω] (y +ℤ[ω] z) ＝ (x *ℤ[ω] y) +ℤ[ω] (x *ℤ[ω] z)
left-distributive-mul-add-ℤ[ω] (a , b) (c , d) (e , f) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a c e)
        ( ( ap
            ( neg-ℤ)
            ( left-distributive-mul-add-ℤ b d f)) ∙
          ( distributive-neg-add-ℤ (b *ℤ d) (b *ℤ f)))) ∙
      ( interchange-law-add-add-ℤ
        ( a *ℤ c)
        ( a *ℤ e)
        ( neg-ℤ (b *ℤ d))
        ( neg-ℤ (b *ℤ f))))
    ( ( ap-add-ℤ
        ( ( ap-add-ℤ
            ( left-distributive-mul-add-ℤ a d f)
            ( right-distributive-mul-add-ℤ c e b)) ∙
          ( interchange-law-add-add-ℤ
            ( a *ℤ d)
            ( a *ℤ f)
            ( c *ℤ b)
            ( e *ℤ b)))
        ( ( ap neg-ℤ (left-distributive-mul-add-ℤ b d f)) ∙
          ( distributive-neg-add-ℤ (b *ℤ d) (b *ℤ f)))) ∙
      ( interchange-law-add-add-ℤ
        ( (a *ℤ d) +ℤ (c *ℤ b))
        ( (a *ℤ f) +ℤ (e *ℤ b))
        ( neg-ℤ (b *ℤ d))
        ( neg-ℤ (b *ℤ f))))

right-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  (x +ℤ[ω] y) *ℤ[ω] z ＝ (x *ℤ[ω] z) +ℤ[ω] (y *ℤ[ω] z)
right-distributive-mul-add-ℤ[ω] x y z =
  ( commutative-mul-ℤ[ω] (x +ℤ[ω] y) z) ∙
  ( ( left-distributive-mul-add-ℤ[ω] z x y) ∙
    ( ap-add-ℤ[ω] (commutative-mul-ℤ[ω] z x) (commutative-mul-ℤ[ω] z y)))

ℤ[ω]-Semigroup : Semigroup lzero
pr1 ℤ[ω]-Semigroup = product-Set ℤ-Set ℤ-Set
pr1 (pr2 ℤ[ω]-Semigroup) = add-ℤ[ω]
pr2 (pr2 ℤ[ω]-Semigroup) = associative-add-ℤ[ω]

ℤ[ω]-Group : Group lzero
pr1 ℤ[ω]-Group = ℤ[ω]-Semigroup
pr1 (pr1 (pr2 ℤ[ω]-Group)) = zero-ℤ[ω]
pr1 (pr2 (pr1 (pr2 ℤ[ω]-Group))) = left-unit-law-add-ℤ[ω]
pr2 (pr2 (pr1 (pr2 ℤ[ω]-Group))) = right-unit-law-add-ℤ[ω]
pr1 (pr2 (pr2 ℤ[ω]-Group)) = neg-ℤ[ω]
pr1 (pr2 (pr2 (pr2 ℤ[ω]-Group))) = left-inverse-law-add-ℤ[ω]
pr2 (pr2 (pr2 (pr2 ℤ[ω]-Group))) = right-inverse-law-add-ℤ[ω]

ℤ[ω]-Ab : Ab lzero
pr1 ℤ[ω]-Ab = ℤ[ω]-Group
pr2 ℤ[ω]-Ab = commutative-add-ℤ[ω]

ℤ[ω]-Ring : Ring lzero
pr1 ℤ[ω]-Ring = ℤ[ω]-Ab
pr1 (pr1 (pr2 ℤ[ω]-Ring)) = mul-ℤ[ω]
pr2 (pr1 (pr2 ℤ[ω]-Ring)) = associative-mul-ℤ[ω]
pr1 (pr1 (pr2 (pr2 ℤ[ω]-Ring))) = one-ℤ[ω]
pr1 (pr2 (pr1 (pr2 (pr2 ℤ[ω]-Ring)))) = left-unit-law-mul-ℤ[ω]
pr2 (pr2 (pr1 (pr2 (pr2 ℤ[ω]-Ring)))) = right-unit-law-mul-ℤ[ω]
pr1 (pr2 (pr2 (pr2 ℤ[ω]-Ring))) = left-distributive-mul-add-ℤ[ω]
pr2 (pr2 (pr2 (pr2 ℤ[ω]-Ring))) = right-distributive-mul-add-ℤ[ω]

ℤ[ω]-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ[ω]-Commutative-Ring = ℤ[ω]-Ring
pr2 ℤ[ω]-Commutative-Ring = commutative-mul-ℤ[ω]
```
