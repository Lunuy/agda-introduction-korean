
module WellOrderingPrinciple where
  
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record Σ (A : Set) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

data ⊥ : Set where


-- Negation
¬_ : Set → Set
¬ P = P → ⊥

¬¬_ : Set → Set
¬¬ P = (P → ⊥) → ⊥

¬¬¬-elim : {A : Set} → ¬¬ (¬ A) → ¬ A
¬¬¬-elim a = λ z₁ → a (λ z₂ → z₂ z₁)

¬¬⊥-elim : ¬¬ ⊥ → ⊥
¬¬⊥-elim a = a (λ z → z)

law-of-excluded-middle : (P : Set) → ¬¬ (P ⊎ (¬ P))
law-of-excluded-middle P a = a (inj₂ (λ x → a (inj₁ x)))

_>>=_ : {A B : Set} → ¬¬ A → (A → ¬¬ B) → ¬¬ B
a >>= f = λ z₁ → a (λ z₂ → f z₂ z₁)

pure : {A : Set} → A → ¬¬ A
pure a = λ f → f a


-- Equality
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl x = x

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl


-- NotEmpty P 는 "자연수의 부분 집합 P는 공집합이 아니다"라는 명제를 나타내는 타입이다.
NotEmpty : (Nat → Set) → Set
NotEmpty P = Σ Nat P


-- a ≤ b라는 명제를 나타내는 타입
data _≤_ : Nat → Nat → Set where
  ≤-zero : {n : Nat}   → zero ≤ n
  ≤-suc  : {n m : Nat} → n ≤ m → (suc n) ≤ (suc m)

-- a < b라는 명제를 나타내는 타입
data _<_ : Nat → Nat → Set where
  <-zero : {n : Nat}   → zero < (suc n)
  <-suc  : {n m : Nat} → n < m → (suc n) < (suc m)

-- a ≤ b가 아니라면 b < a이다.
¬≤-to-¬¬< : {a b : Nat} → ¬ (a ≤ b) → ¬¬ (b < a)
¬≤-to-¬¬< {zero} {zero} f = λ _ → f ≤-zero
¬≤-to-¬¬< {zero} {suc b} f = λ _ → f ≤-zero
¬≤-to-¬¬< {suc a} {zero} f = λ z → z <-zero
¬≤-to-¬¬< {suc a} {suc b} f = do
  b<a ← ¬≤-to-¬¬< {a} {b} (λ x → f (≤-suc x))
  pure (<-suc b<a)

-- a < 1 + b라면 a < b 또는 a = b이다.
<-right-suc-split : {a b : Nat} → a < (suc b) → (a < b) ⊎ (a ≡ b)
<-right-suc-split {zero}  {zero}  _         = inj₂ refl
<-right-suc-split {zero}  {suc _} _         = inj₁ <-zero
<-right-suc-split {suc a} {suc b} (<-suc c) = f (<-right-suc-split c)
  where
  f : (a < b) ⊎ (a ≡ b) → (suc a < suc b) ⊎ (suc a ≡ suc b)
  f (inj₁ x) = inj₁ (<-suc x)
  f (inj₂ x) = inj₂ (cong suc x)

-- 강한 수학적 귀납법
strong-nat-induction : {P : Nat → Set} → ((n : Nat) → ((m : Nat) → m < n → P m) → P n) → ((n : Nat) → P n)
strong-nat-induction {P} f n = con (suc n) n (n-<-suc-n n)
  where
    con : (n : Nat) → ((m : Nat) → m < n → P m)
    con zero m ()
    con (suc n) m a = g (<-right-suc-split a)
      where
      g : (m < n) ⊎ (m ≡ n) → P m
      g (inj₁ x)    = con n m x
      g (inj₂ refl) = f n (con n)
    
    n-<-suc-n : (n : Nat) → n < suc n
    n-<-suc-n zero = <-zero
    n-<-suc-n (suc n) = <-suc (n-<-suc-n n)

-- ¬¬Min P n은 "P의 최소값이 n이다"라는 명제를 나타내는 타입
record ¬¬Min (P : Nat → Set) (n : Nat) : Set where
  field
    min  : (m : Nat) → P m → ¬¬ (n ≤ m)
    in-P : ¬¬ (P n)

-- Well-ordering principle
-- 공집합이 아닌 집합 P는 최소값을 갖는다.
well-ordering-principle : (P : Nat → Set) → NotEmpty P → ¬¬ (Σ Nat (¬¬Min P))
well-ordering-principle P not-empty-P = λ a → well-ordering-principle-contrapositive a not-empty-P
  where
    h : (n : Nat) → ((m : Nat) → m < n → ¬ P m) → (P n) → ¬¬Min P n
    h n f p-n = record
      { min = min
      ; in-P = λ z → z p-n
      }
      where
      min : (m : Nat) → P m → ¬¬ (n ≤ m)
      min m p-m = λ a → ¬¬⊥-elim (
        do
          b ← (¬≤-to-¬¬< a)
          pure (f m b p-m)
        )

    f : ¬ (Σ Nat (¬¬Min P)) → (n : Nat) → ((m : Nat) → m < n → ¬ P m) → ¬ P n
    f a zero f = λ z →
      a
        (record
          { fst = zero
          ; snd = record
            { min = λ m _ z → z ≤-zero
            ; in-P = pure z
            }
          }
        )
    f a (suc k) f = λ z →
      a record
        { fst = suc k
        ; snd = record
          { min = λ m p-m → do
            c ← (¬¬Min.min (h (suc k) f z)) m p-m
            pure c
          ; in-P = pure z
          }
        }

    g : ((n : Nat) → ¬ P n) → ¬ NotEmpty P
    g a record { fst = fst ; snd = snd } = a fst snd
    
    well-ordering-principle-contrapositive : ¬ (Σ Nat (¬¬Min P)) → ¬ NotEmpty P
    well-ordering-principle-contrapositive a = g (strong-nat-induction {λ n → ¬ P n} (f a))